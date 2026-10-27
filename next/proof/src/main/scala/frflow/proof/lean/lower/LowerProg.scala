package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Prog, Progs}
import frflow.core.term.Stated
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed

/** A flow's steps as the lines of a `do` block, as today's `LeanPrinter.block`: the steps' structure here, each term
  * printed from itself (`Printed`) in the scope the steps' variables are named in, below `depth` inputs.
  */
final class LowerProg(env: LowerEnv, depth: Int):
  import Atoms.name
  private type L[A] = State[Naming, A]
  private type P = Prog[Stated[?]]

  def block(p: P): L[List[DoLine]] = p match
    case Prog.Pure(t)                => term(t).map(x => List(DoLine.Step(LExpr.App(name("pure"), List(x)))))
    case Prog.Atomic(body)           => block(body)
    case Prog.Bind(Prog.Bind(a, x, r), y, rest) if y.wildcard => block(Prog.Bind(a, x, Prog.Bind(r, y, rest)))
    case Prog.Bind(Prog.Let(x, v, r), y, rest) if y.wildcard  => block(Prog.Let(x, v, Prog.Bind(r, y, rest)))
    case Prog.Bind(first, x, rest)   => (bound(first, x), block(rest)).mapN(_ ++ _)
    case Prog.Let(x, v, rest)        =>
      (term(v), Naming.bind(x), block(rest)).mapN((tv, n, r) => DoLine.Let(n, tv) :: r)
    case Prog.Loop(xs, x, body)      =>
      (term(xs), Naming.bind(x), block(body)).mapN((r, n, b) => List(DoLine.For(n, r, b)))
    case Prog.Branch(c, a, b)        => (term(c), block(a), block(b)).mapN((x, y, z) => List(DoLine.Branch(x, y, z)))
    case other if Progs.sequential(other) != other => block(Progs.sequential(other))
    case one                         => step(one).map(s => List(DoLine.Step(s)))

  private def term(t: Stated[?]): L[LExpr] = State.inspect(n => Printed.term(env, n, depth)(t))

  /** `first`, bound to `x` (dropped when `x` is a wildcard). A transaction is its body: on the models, a run is
    * already one step of the world.
    */
  private def bound(first: P, x: Binder): L[List[DoLine]] =
    if x.wildcard then dropped(first)
    else first match
      case Prog.Atomic(body) => bound(body, x)
      case _                 => named(first, x)

  private def named(first: P, x: Binder): L[List[DoLine]] =
    Naming.bind(x).flatMap(n => first match
      case Prog.Bind(_, _, _) | Prog.Let(_, _, _) | Prog.Loop(_, _, _) | Prog.Branch(_, _, _) =>
        block(first).map(b => List(DoLine.BindBlock(Some(n), b)))
      case _ => step(first).map(s => List(DoLine.Bind(n, s))))

  private def dropped(first: P): L[List[DoLine]] = first match
    case Prog.Atomic(body)                         => dropped(body)
    case Prog.Loop(_, _, _) | Prog.Branch(_, _, _) => block(first)
    case Prog.Bind(_, _, _) | Prog.Let(_, _, _)    => block(first).map(b => List(DoLine.BindBlock(None, b)))
    case _                                         => step(first).map(s => List(DoLine.Step(s)))

  /** One step, on a line of its own. */
  private def step(p: P): L[LExpr] = p match
    case Prog.Pure(t)              => term(t).map(x => LExpr.App(name("pure"), List(x)))
    case Prog.Call(b, op, as, _)   =>
      as.traverse(term).map(LExpr.App(LExpr.Const(List(env.boundaryClass(b), Names.ident(op.value))), _))
    case Prog.Read(_)              => State.pure(name("get"))
    case Prog.Write(_, s)          => term(s).map(x => LExpr.App(name("set"), List(x)))
    case Prog.Modify(_, x, next)   => (Naming.bind(x), term(next)).mapN(modify)
    case _                         => ??? // raise, catch (`tryCatchThe`), collect and accumulate (`mapM`, `foldlM`)

  private def modify(n: LeanName, b: LExpr): LExpr =
    LExpr.App(name("modify"), List(LExpr.Paren(LExpr.Fun(List(LBinder.Bare(n)), b))))
