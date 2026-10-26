package frflow.eval.run

import cats.effect.kernel.Sync
import cats.Parallel
import cats.syntax.all.*
import frflow.core.expr.{Expr, Prog}
import frflow.core.name.{BoundaryName, OpName, SymbolName}
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Fresh}
import frflow.dsl.flow.{Bound, Flow}
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.eval.{Denote, Env, Fn, ScalaValue}

/** The one interpreter of flows: a proven flow's `Prog`, and the DSL flows an implementation's operations give. A
  * call's arguments are passed to the implementation as run-time symbols bound in the `Env` (`$argN`), typed by the
  * operation's signature, so no value is reified; every flow the developer's code builds is built in a `Fresh` scope
  * (`built`). `Parallel` and `atomically` say how concurrent steps run; `pause` comes before every call.
  */
final class FlowInterpreter[F[_]](denote: Denote, bound: Map[BoundaryName, Bound],
    atomically: [A] => F[A] => F[A], pause: F[Unit])(using F: Sync[F], P: Parallel[F]):
  def prog(p: Prog, env: Env): F[ScalaValue] = p match
    case Prog.Pure(t)              => value(t, env)
    case Prog.Bind(first, x, rest) => prog(first, env).flatMap(v => prog(rest, env.bind(x.id, v)))
    case Prog.Let(x, v, rest)      => value(v, env).flatMap(a => prog(rest, env.bind(x.id, a)))
    case Prog.Branch(c, a, b)      => value(c, env).flatMap(v => if Fn.bool(v) then prog(a, env) else prog(b, env))
    case Prog.Call(b, op, as, _)   => as.traverse(value(_, env)).flatMap(vs => call(b, op, vs, env)).map(_._1)
    case Prog.Par(l, x, r, y)      => (prog(l, env), prog(r, env)).parTupled.flatMap((a, b) =>
                                        val both = env.bind(x.id, a).bind(y.id, b)
                                        value(Expr.Tuple(List(Expr.Var(x), Expr.Var(y))), both))
    case Prog.Atomic(body)         => atomically(prog(body, env))
    case _                         => ??? // loops, collect, accumulate, catch, raise, `ParEach` (`parTraverse`)

  /** An implementation's flow: its result, and its type (a step's result becomes a term of the next step). */
  def flow(f: Flow[?], env: Env): F[(ScalaValue, Ty)] = f match
    case Flow.Pure(t)              => value(t.expr, env).map(_ -> t.leanType.ty)
    case b: Flow.Bind[x, ?]        => flow(b.first, env).flatMap { (v, ty) =>
                                        val (s, inner) = env.fresh(v)
                                        flow(built(b.next(symbol(s, ty).asInstanceOf[Term[x]])), inner) } // typed `ty`
    case Flow.Effect(args, run, r) => args.traverse(a => value(a.expr, env))
                                        .flatMap(vs => F.delay(ScalaValue(run(vs.map(_.unwrap)))).map(_ -> r.ty))
    case Flow.Call(b, op, as)      => as.traverse(a => value(a.expr, env)).flatMap(call(b, op, _, env))

  private def call(b: BoundaryName, op: OpName, vs: List[ScalaValue], env: Env): F[(ScalaValue, Ty)] =
    for
      impl <- bound.get(b).liftTo[F](FlowError.NotBound(b))
      sig  <- impl.ops.find(_.name == op).liftTo[F](FlowError.NoOperation(b, op))
      _    <- pause
      out  <- arguments(vs.zip(sig.params.map(_._2)), env) match
                case (terms, inner) => flow(built(impl.call(op, terms)), inner)
    yield out

  /** Each value bound to a fresh run-time symbol of its type, and the terms of those symbols. */
  private def arguments(vs: List[(ScalaValue, Ty)], env: Env): (List[Term[Any]], Env) =
    vs.foldLeft((List.empty[Term[Any]], env)) { case ((ts, e), (v, t)) =>
      val (s, next) = e.fresh(v)
      (ts :+ symbol(s, t), next)
    }

  /** A flow the developer's code builds now (an operation's, or a continuation's): in a `Fresh` scope of its own, so
    * its terms may bind variables (`xs.filter(…)`).
    */
  private def built[A](f: => Flow[A]): Flow[A] = Fresh.within(f)

  /** A run-time symbol's term: never lowered, only evaluated in the run's `Env`. */
  private def symbol(s: SymbolName, ty: Ty): Term[Any] =
    Term(Expr.Sym(s, ty), Notes.of(Declarations.none))(using LeanType.of(ty))

  private def value(e: Expr, env: Env): F[ScalaValue] =
    F.defer(denote(e).run(env).leftMap(FlowError.NotEvaluated(_)).liftTo[F])
