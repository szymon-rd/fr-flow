package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Exprs, Prog, Progs}
import frflow.core.term.Stated
import frflow.core.term.interpret.ToExpr
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed

/** A flow's steps as the lines of a `do` block, as today's `LeanPrinter.block`: the steps' structure here, each term
  * printed from itself (`Printed`) in the scope the steps' variables are named in, below `depth` inputs. A concurrent
  * step is its sequential reading (`Progs.sequential`), bound as a whole; its commutation is `commute_i`'s.
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
    case Prog.Collect(_, _, _) | Prog.Accumulate(_, _, _, _, _) => over(p, None).map(List(_))
    case Prog.Catch(_, _, _, _)      => caught(p, None).map(List(_))
    case other if Progs.sequential(other) != other => block(Progs.sequential(other))
    case one                         => step(one).map(s => List(DoLine.Step(s)))

  private def term(t: Stated[?]): L[LExpr] = State.inspect(n => Printed.term(env, n, depth)(t))

  /** `first`, bound to `x` (dropped when `x` is a wildcard). A transaction is its body: on the models, a run is
    * already one step of the world; a concurrent step is bound as its sequential reading.
    */
  private def bound(first: P, x: Binder): L[List[DoLine]] =
    val one = Progs.sequential(first)
    if x.wildcard then dropped(one)
    else if one != first then Naming.bind(x).flatMap(n => block(one).map(b => List(DoLine.BindBlock(Some(n), b))))
    else named(first, x)

  private def named(first: P, x: Binder): L[List[DoLine]] =
    Naming.bind(x).flatMap(n => first match
      case Prog.Bind(_, _, _) | Prog.Let(_, _, _) | Prog.Loop(_, _, _) | Prog.Branch(_, _, _) =>
        block(first).map(b => List(DoLine.BindBlock(Some(n), b)))
      case Prog.Collect(_, _, _) | Prog.Accumulate(_, _, _, _, _) => over(first, Some(n)).map(List(_))
      case Prog.Catch(_, _, _, _) => caught(first, Some(n)).map(List(_))
      case _ => step(first).map(s => List(DoLine.Bind(n, s))))

  private def dropped(first: P): L[List[DoLine]] = first match
    case Prog.Loop(_, _, _) | Prog.Branch(_, _, _) | Prog.Catch(_, _, _, _) => block(first)
    case Prog.Bind(_, _, _) | Prog.Let(_, _, _)    => block(first).map(b => List(DoLine.BindBlock(None, b)))
    case Prog.Collect(_, _, _) | Prog.Accumulate(_, _, _, _, _) =>
      over(first, Some(Names.builtin("_"))).map(List(_))
    case _                                         => step(first).map(s => List(DoLine.Step(s)))

  /** `xs.mapM fun x => do …` and `xs.foldlM (init := z) fun acc x => do …`, after `lead` (a binding, or none). */
  private def over(p: P, lead: Option[LeanName]): L[DoLine] = p match
    case Prog.Collect(xs, x, body) =>
      (term(xs), Naming.bind(x), block(body)).mapN((r, n, b) => DoLine.Traverse(lead, LExpr.Dot(r, "mapM"), List(n), b))
    case Prog.Accumulate(xs, z, acc, x, body) =>
      (term(xs), term(z), Naming.bind(acc), Naming.bind(x), block(body)).mapN { (r, tz, a, n, b) =>
        DoLine.Traverse(lead, LExpr.Named(LExpr.Dot(r, "foldlM"), Names.builtin("init"), tz), List(a, n), b)
      }
    case other => block(other).map(DoLine.BindBlock(lead, _))

  /** `tryCatchThe E (do …) (fun e => do …)`, after `lead` (a binding, or none). */
  private def caught(p: P, lead: Option[LeanName]): L[DoLine] = p match
    case Prog.Catch(body, error, x, handler) =>
      (block(body), if x.wildcard then State.pure(None) else Naming.bind(x).map(Some(_)), block(handler)).mapN(
        (b, n, h) => DoLine.TryCatch(lead, LowerType(error), b, n, h))
    case other => block(other).map(DoLine.BindBlock(lead, _))

  /** One step, on a line of its own. */
  private def step(p: P): L[LExpr] = p match
    case Prog.Pure(t)              => term(t).map(x => LExpr.App(name("pure"), List(x)))
    case Prog.Call(b, op, as, _)   =>
      as.traverse(term).map(LExpr.App(LExpr.Const(List(env.boundaryClass(b), Names.ident(op.value))), _))
    case Prog.Read(_)              => State.pure(name("get"))
    case Prog.Write(_, s)          => term(s).map(x => LExpr.App(name("set"), List(x)))
    case Prog.Modify(_, x, next)   => (Naming.bind(x), term(next)).mapN(modify)
    case Prog.Raise(e)             =>
      term(e).map(x => LExpr.App(name("throwThe"), List(LowerType(Exprs.typeOf(ToExpr.of(e.run, depth))), x)))
    case other                     =>
      throw IllegalStateException(s"FrFlow bug: a compound step lowered as one line: ${other.getClass.getSimpleName}")

  private def modify(n: LeanName, b: LExpr): LExpr =
    LExpr.App(name("modify"), List(LExpr.Paren(LExpr.Fun(List(LBinder.Bare(n)), b))))
