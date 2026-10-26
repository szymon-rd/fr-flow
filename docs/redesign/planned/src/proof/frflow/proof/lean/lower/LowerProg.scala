package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Prog, Progs}
import frflow.proof.lean.ast.*

/** A flow's steps as the lines of a `do` block, as today's `LeanPrinter.block`. */
final class LowerProg(lower: Lower, env: LowerEnv):
  import Atoms.name
  private type L[A] = State[Naming, A]

  def block(p: Prog): L[List[DoLine]] = p match
    case Prog.Pure(t)                => lower.expr(t).map(x => List(DoLine.Step(LExpr.App(name("pure"), List(x)))))
    case Prog.Bind(Prog.Bind(a, x, r), y, rest) if y.wildcard => block(Prog.Bind(a, x, Prog.Bind(r, y, rest)))
    case Prog.Bind(Prog.Let(x, v, r), y, rest) if y.wildcard  => block(Prog.Let(x, v, Prog.Bind(r, y, rest)))
    case Prog.Bind(first, x, rest)   => (bound(first, x), block(rest)).mapN(_ ++ _)
    case Prog.Let(x, v, rest)        =>
      (lower.expr(v), Naming.bind(x), block(rest)).mapN((tv, n, r) => DoLine.Let(n, tv) :: r)
    case Prog.Loop(xs, x, body)      =>
      (lower.expr(xs), Naming.bind(x), block(body)).mapN((r, n, b) => List(DoLine.For(n, r, b)))
    case Prog.Branch(c, a, b)        =>
      (lower.expr(c), block(a), block(b)).mapN((x, y, z) => List(DoLine.Branch(x, y, z)))
    case other if Progs.sequential(other) != other => block(Progs.sequential(other))
    case one                         => step(one).map(s => List(DoLine.Step(s)))

  /** `first`, bound to `x` (dropped when `x` is a wildcard). */
  private def bound(first: Prog, x: Binder): L[List[DoLine]] =
    if x.wildcard then dropped(first)
    else Naming.bind(x).flatMap(n => first match
      case Prog.Bind(_, _, _) | Prog.Let(_, _, _) | Prog.Loop(_, _, _) | Prog.Branch(_, _, _) =>
        block(first).map(b => List(DoLine.BindBlock(Some(n), b)))
      case _ => step(first).map(s => List(DoLine.Bind(n, s))))

  private def dropped(first: Prog): L[List[DoLine]] = first match
    case Prog.Loop(_, _, _) | Prog.Branch(_, _, _) => block(first)
    case Prog.Bind(_, _, _) | Prog.Let(_, _, _)    => block(first).map(b => List(DoLine.BindBlock(None, b)))
    case _                                         => step(first).map(s => List(DoLine.Step(s)))

  /** One step, on a line of its own. */
  private def step(p: Prog): L[LExpr] = p match
    case Prog.Pure(t)              => lower.expr(t).map(x => LExpr.App(name("pure"), List(x)))
    case Prog.Call(b, op, as, _)   =>
      as.traverse(lower.expr).map(LExpr.App(LExpr.Const(List(env.boundaryClass(b), Names.ident(op.value))), _))
    case Prog.Read(_)              => State.pure(name("get"))
    case Prog.Write(_, s)          => lower.expr(s).map(x => LExpr.App(name("set"), List(x)))
    case Prog.Modify(_, x, next)   => (Naming.bind(x), lower.expr(next)).mapN(modify)
    case _                         => ??? // raise, catch (`tryCatchThe`), collect and accumulate (`mapM`, `foldlM`)

  private def modify(n: LeanName, b: LExpr): LExpr =
    LExpr.App(name("modify"), List(LExpr.Paren(LExpr.Fun(List(LBinder.Bare(n)), b))))
