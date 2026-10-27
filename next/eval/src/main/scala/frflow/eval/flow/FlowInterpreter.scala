package frflow.eval.flow

import cats.MonadThrow
import cats.effect.kernel.Async
import cats.effect.std.Mutex
import cats.syntax.all.*
import frflow.core.expr.{Binder, Exprs, Prog}
import frflow.core.term.Stated
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.eval.{Env, Fn, Raised, ScalaValue, Semantics}

/** A recorded program's `Prog` run in Scala, its terms by the evaluator, against a `World`: on the models (flow
  * examples, and the model each implementation is tested against), or on the adapters (the interleavings tests).
  * A program's error is raised in `F` as `Raised` (its value and type), caught by a handler of its type;
  * `Scheduling` says how concurrent steps run.
  */
final class FlowInterpreter[F[_]](semantics: Semantics, world: World[F], scheduling: Scheduling[F],
    branched: (Prog[Stated[?]], Boolean) => F[Unit])(using F: MonadThrow[F]):
  private type P = Prog[Stated[?]]

  /** The program's outcome: the error it failed with (`Left`), or its result. */
  def outcome(p: P, env: Env): F[Either[ScalaValue, ScalaValue]] =
    prog(p, env).map(_.asRight[ScalaValue]).recover { case r: Raised => Left(r.error) }

  def prog(p: P, env: Env): F[ScalaValue] = p match
    case Prog.Pure(t)              => value(t, env)
    case Prog.Bind(first, x, rest) => prog(first, env).flatMap(v => prog(rest, env.bind(x.id, v)))
    case Prog.Let(x, v, rest)      => value(v, env).flatMap(a => prog(rest, env.bind(x.id, a)))
    case br @ Prog.Branch(c, a, b) => value(c, env).flatMap(v =>
        branched(br, Fn.bool(v)) *> (if Fn.bool(v) then prog(a, env) else prog(b, env)))
    case Prog.Call(b, op, as, _)   => as.traverse(value(_, env)).flatMap(world.call(b, op, _))
    case Prog.Read(m)              => world.read(m)
    case Prog.Write(m, s)          => value(s, env).flatMap(world.write(m, _)).as(unit)
    case Prog.Modify(m, x, next)   =>
      world.read(m).flatMap(s => value(next, env.bind(x.id, s))).flatMap(world.write(m, _)).as(unit)
    case Prog.Raise(e)             => value(e, env).flatMap(v => F.raiseError(Raised(v, typeOf(e))))
    case Prog.Catch(body, t, x, h) => prog(body, env).recoverWith {
        case r: Raised if r.ty == t => prog(h, env.bind(x.id, r.error))
      }
    case loop @ (Prog.Loop(_, _, _) | Prog.Collect(_, _, _) | Prog.Accumulate(_, _, _, _, _)) => loops(loop, env)
    case concurrent                => scheduled(concurrent, env)

  /** The steps over a list's elements, one after another. */
  private def loops(p: P, env: Env): F[ScalaValue] = p match
    case Prog.Loop(xs, x, body)    => list(xs, env).flatMap(_.traverse_(v => prog(body, env.bind(x.id, v)))).as(unit)
    case Prog.Collect(xs, x, body) => list(xs, env).flatMap(_.traverse(v => prog(body, env.bind(x.id, v)))).map(many)
    case Prog.Accumulate(xs, z, acc, x, body) =>
      (list(xs, env), value(z, env)).tupled.flatMap((vs, init) =>
        vs.foldLeftM(init)((a, v) => prog(body, env.bind(acc.id, a).bind(x.id, v))))
    case other                     => prog(other, env)

  /** The concurrent steps, as `scheduling` runs them. */
  private def scheduled(p: P, env: Env): F[ScalaValue] = p match
    case Prog.Par(l, _, r, _)      =>
      scheduling.both(prog(l, env), prog(r, env)).map((a, b) => ScalaValue((a.unwrap, b.unwrap)))
    case Prog.ParEach(xs, x, body, limit) =>
      list(xs, env).flatMap(scheduling.each(limit)(_)(v => prog(body, env.bind(x.id, v)))).map(many)
    case Prog.Race(l, r, reading)  =>
      val read = prog(reading, env).map(v => Fn.as[Either[Any, Any]](v).bimap(ScalaValue(_), ScalaValue(_)))
      scheduling.race(prog(l, env), prog(r, env), read).map(e => ScalaValue(e.bimap(_.unwrap, _.unwrap)))
    case Prog.Guard(body, _, fin, reading) =>
      scheduling.guard(prog(body, env), prog(fin, env).void, prog(reading, env))
    case Prog.Atomic(body)         => scheduling.atomically(prog(body, env))
    case other                     => prog(other, env)

  private def value(t: Stated[?], env: Env): F[ScalaValue] =
    F.unit.flatMap(_ => semantics.term(t)(env).leftMap(FlowError.NotEvaluated(_)).liftTo[F])
  private def list(t: Stated[?], env: Env): F[List[ScalaValue]] = value(t, env).map(v => Fn.list(v).map(ScalaValue(_)))
  private def typeOf(t: Stated[?]): Ty = Exprs.typeOf(ToExpr.of(t.run))
  private def many(vs: List[ScalaValue]): ScalaValue = ScalaValue(vs.map(_.unwrap))
  private val unit: ScalaValue = ScalaValue(())

object FlowInterpreter:
  /** Steps one after the other, as Lean reads them: the models' reading (a pure state monad in examples and tests,
    * `ProgramRun`).
    */
  def sequential[F[_]: MonadThrow](semantics: Semantics, world: World[F]): FlowInterpreter[F] =
    watched(semantics, world, (_, _) => MonadThrow[F].unit)

  /** The same, each branch taken said to `branched` (what a model test reaches of the model's steps). */
  def watched[F[_]: MonadThrow](semantics: Semantics, world: World[F], branched: (Prog[Stated[?]], Boolean) => F[Unit])
      : FlowInterpreter[F] =
    FlowInterpreter(semantics, world, Scheduling.sequential[F], branched)

  /** Branches at once, and `atomically` under one lock (`IO` in the interleavings tests). */
  def concurrent[F[_]: Async](semantics: Semantics, world: World[F]): F[FlowInterpreter[F]] =
    Mutex[F].map(lock =>
      FlowInterpreter(semantics, world, Scheduling.concurrent[F]([A] => (fa: F[A]) => lock.lock.surround(fa)),
        (_, _) => Async[F].unit))

  /** The binders a model's operation is given its arguments at. */
  def arguments(params: List[Binder], args: List[ScalaValue]): Env =
    params.zip(args).foldLeft(Env.of(frflow.core.code.Values.none))((e, xa) => e.bind(xa._1.id, xa._2))
