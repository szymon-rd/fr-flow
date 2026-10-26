package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Arm, Binder, Expr, Exprs, Lambda, Quantifier, Side}
import frflow.core.name.{CtorName, DefName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.proof.lean.ast.*

/** An expression of the IR as a Lean term: today's `LeanPrinter.expr`, same parentheses and names, on typed values. */
final class Lower(env: LowerEnv):
  type L[A] = State[Naming, A]
  import Atoms.{call, const, name}
  import LExpr.{Dot, Paren}
  private val prims = LowerPrim(this)
  private val values = LowerValue(env)
  private val progs = LowerProg(this, env)

  /** A lambda's parameters, typed, and its body: a declaration's binders and value. */
  def lambda(l: Lambda): L[(List[LBinder], LExpr)] =
    (l.params.traverse(typed), expr(l.body)).tupled

  def typed(x: Binder): L[LBinder] = Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty)))

  def expr(e: Expr): L[LExpr] = e match
    case Expr.Var(x)                => Naming.of(x).map(LExpr.Name(_))
    case Expr.Lit(v, t)             => values(v, t)
    case Expr.Sym(n, _)             => State.pure(LExpr.Name(Names.ident(n.value)))
    case Expr.Call(d, as, _)        => as.traverse(expr).map(call(head(d), _))
    case Expr.Apply(f, as, _)       => (expr(f), as.traverse(expr)).mapN(call)
    case Expr.Fun(l)                => lambda(l).map((bs, b) => Paren(LExpr.Fun(bs, b)))
    case Expr.Quant(q, xs, b)       => (xs.traverse(typed), expr(b)).mapN((bs, x) => Paren(quant(q, bs, x)))
    case Expr.If(c, a, b)           => (expr(c), expr(a), expr(b)).mapN((x, y, z) => Paren(LExpr.If(x, y, z)))
    case Expr.Match(on, arms, _)    => (expr(on), arms.traverse(arm)).mapN((s, as) => Paren(LExpr.Match(s, as)))
    case Expr.Let(x, v, b)          => (expr(v), Naming.bind(x), expr(b)).mapN((tv, n, tb) =>
                                         Paren(LExpr.Let(n, LowerType(x.ty), tv, tb)))
    case Expr.Field(on, d, i, _)    => expr(on).map(Dot(_, fieldName(d, i)))
    case Expr.Copy(on, d, us)       => copy(on, d, us)
    case Expr.Make(d, c, as)        => as.traverse(expr).map(call(Lower.ctor(d, c), _))
    case Expr.Tuple(es)             => es.traverse(expr).map(LExpr.Tuple(_))
    case Expr.Proj(on, k, _)        => expr(on).map(projection(_, k, arity(on)))
    case Expr.SomeOf(a)             => expr(a).map(x => call(name("some"), List(x)))
    case Expr.Inject(s, a, _)       => expr(a).map(x => call(const(s"Except.${side(s)}"), List(x)))
    case Expr.ListOf(es, _)         => es.traverse(expr).map(LExpr.ListLit(_))
    case Expr.Iterate(how, on, x, b, _) => LowerIterate(this)(how, on, x, b)
    case f: Expr.Fold               => fold(f)
    case Expr.Prim(op, as, _)       => prims(op, as)
    case Expr.Do(p, _)              => progs.block(p).map(LExpr.Do(_, 4))
    case Expr.RunOn(c, w, err, _)   => runOn(c, w, err)
    case Expr.Part(w, m, _)         => expr(w).map(Dot(_, env.modelField(m).text))

  private def quant(q: Quantifier, bs: List[LBinder], b: LExpr) = q match
    case Quantifier.Forall => LExpr.Forall(bs, b)
    case Quantifier.Exists => LExpr.Exists(bs, b)

  private def side(s: Side) = if s == Side.Error then "error" else "ok"

  /** `K.d`, or `(K.d t1 … tk)` applied to the open terms the define is over. */
  private def head(d: DefName): LExpr =
    val c = LExpr.Const(Names.path(env.kb.value, d.value))
    env.openTerms(d) match
      case Nil   => c
      case terms => call(c, terms.map(LExpr.Name(_)))

  /** `(List.foldl (fun (acc : A) (x : T) => b) z xs)`. */
  private def fold(f: Expr.Fold): L[LExpr] =
    (expr(f.over), expr(f.init), typed(f.acc), typed(f.x), expr(f.body)).mapN((r, init, a, y, body) =>
      call(const("List.foldl"), List(Paren(LExpr.Fun(List(a, y), body)), init, r)))

  private def runOn(c: Expr, w: Expr, err: Option[Ty]): L[LExpr] = (expr(c), expr(w)).mapN { (x, y) =>
    val run = err.fold(const("FrFlow.runOn"))(e =>
      LExpr.Named(const("FrFlow.runOnE"), Names.builtin("ε"), LowerType(e)))
    call(run, List(x, y))
  }

  /** `{ r with f := v, … }`, leaving out a field set to itself; `r` when none is left. */
  private def copy(on: Expr, d: TypeName, us: List[(Int, Expr)]): L[LExpr] =
    for
      r  <- expr(on)
      vs <- us.traverse((i, v) => expr(v).map(x => (Names.ident(fieldName(d, i)), x)))
    yield vs.filterNot((f, v) => v == Dot(r, f.text)) match
      case Nil     => r
      case updates => LExpr.Update(r, updates)

  /** Lean's `A × B × C` is `A × (B × C)`: the k-th of n is k-1 steps right, then left (but the last). */
  private def projection(on: LExpr, k: Int, n: Int): LExpr =
    val right = (1 until k).foldLeft(on)((e, _) => Dot(e, "2"))
    if k == n then right else Dot(right, "1")

  private def arity(on: Expr): Int = Exprs.typeOf(on) match
    case Ty.TupleOf(ts) => ts.size
    case _              => throw IllegalStateException("FrFlow bug: a projection of a value that is not a tuple")

  private def arm(a: Arm): L[(LExpr, LExpr)] = (LowerPattern(a.pattern), expr(a.body)).tupled

  private def fieldName(d: TypeName, i: Int): String = env.data(d) match
    case Some(DataType.Product(_, _, fs)) => Names.ident(fs(i).name).text
    case _ => throw IllegalStateException(s"FrFlow bug: field $i of ${d.value}, which is not a case class")

object Lower:
  /** `Event.Expired`: a constructor, qualified by its type. */
  def ctor(d: TypeName, c: CtorName): LExpr = Atoms.const(s"${d.value}.${c.value}")
