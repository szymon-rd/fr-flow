package frflow.eval.flow

import cats.effect.kernel.{Async, Sync}
import cats.effect.kernel.implicits.parallelForGenSpawn
import cats.effect.std.Mutex
import cats.Parallel
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.term.Stated
import frflow.eval.{Env, Fn, ScalaValue, Semantics}

/** A recorded program's `Prog` run in Scala, its terms by the evaluator, against a `World`: on the models (flow
  * examples, and the model each implementation is tested against), or on the adapters with a pause before each call
  * (the interleavings tests).
  * `Parallel` and `atomically` say how concurrent steps run.
  */
final class FlowInterpreter[F[_]](semantics: Semantics, world: World[F], atomically: [A] => F[A] => F[A])(
    using F: Sync[F], P: Parallel[F]):
  def prog(p: Prog[Stated[?]], env: Env): F[ScalaValue] = p match
    case Prog.Pure(t)              => value(t, env)
    case Prog.Bind(first, x, rest) => prog(first, env).flatMap(v => prog(rest, env.bind(x.id, v)))
    case Prog.Let(x, v, rest)      => value(v, env).flatMap(a => prog(rest, env.bind(x.id, a)))
    case Prog.Branch(c, a, b)      => value(c, env).flatMap(v => if Fn.bool(v) then prog(a, env) else prog(b, env))
    case Prog.Call(b, op, as, _)   => as.traverse(value(_, env)).flatMap(world.call(b, op, _))
    case Prog.Read(m)              => world.read(m)
    case Prog.Write(m, s)          => value(s, env).flatMap(world.write(m, _)).as(ScalaValue(()))
    case Prog.Modify(m, x, next)   =>
      world.read(m).flatMap(s => value(next, env.bind(x.id, s))).flatMap(world.write(m, _)).as(ScalaValue(()))
    case Prog.Par(l, _, r, _)      => (prog(l, env), prog(r, env)).parMapN((a, b) => ScalaValue((a.unwrap, b.unwrap)))
    case Prog.Atomic(body)         => atomically(prog(body, env))
    case _                         => ??? // loops, collect, accumulate, catch, raise, `ParEach`, `Race`, `Guard`

  private def value(t: Stated[?], env: Env): F[ScalaValue] =
    F.defer(semantics.term(t)(env).leftMap(FlowError.NotEvaluated(_)).liftTo[F])

object FlowInterpreter:
  /** Steps one after the other: the models' reading (`SyncIO` in examples). */
  def sequential[F[_]: Sync](semantics: Semantics, world: World[F]): FlowInterpreter[F] =
    FlowInterpreter(semantics, world, [A] => (fa: F[A]) => fa)(using Sync[F], Parallel.identity[F])

  /** Branches at once, and `atomically` under one lock (`IO` in the interleavings tests). */
  def concurrent[F[_]: Async](semantics: Semantics, world: World[F]): F[FlowInterpreter[F]] =
    Mutex[F].map(lock => FlowInterpreter(semantics, world, [A] => (fa: F[A]) => lock.lock.surround(fa)))
