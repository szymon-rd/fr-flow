package frflow.proof.lean.term

import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.*
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LExprs, LowerEnv, LowerType, LowerValue}

/** The Lean printer of terms, the only one: LNCS 7470 §3.2's `S` interpreter (there `S a = Int -> String`, the binder
  * depth in, the text out), here the scope in and Lean's AST out. Every compound term in parentheses; application
  * flattened (`(Rooms.covers b t)`); a named definition called by name, its body printed once as its `def`
  * (`Printed.define`); a field of a constructor is its argument, so a match arm's case reads as its fields' names.
  */
final class LeanTerm(env: LowerEnv, standing: Map[SymbolName, LExpr] = Map.empty) extends Sym[LeanTerm.S],
    LeanFinite:
  import Atoms.{call, const, name}
  import LExpr.{Infix, Paren}
  private type S[A] = LeanTerm.S[A]
  private val constants = LowerValue(env)
  private lazy val (outcomes, byName) = (Outcomes(env, standing), standing.map((n, e) => Names.ident(n.value) -> e))

  def bool(b: Boolean): S[Boolean] = _ => name(if b then "True" else "False")
  def and(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.And, a, b)
  def or(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.Or, a, b)
  def not(a: S[Boolean]): S[Boolean] = s => Paren(LExpr.Prefix(LPrefix.Not, a(s)))
  def implies(a: S[Boolean], b: S[Boolean]): S[Boolean] = infix(LOp.Arrow, a, b)
  def cond[A](c: S[Boolean], t: S[A], e: S[A]): S[A] = s => Paren(LExpr.If(c(s), t(s), e(s)))
  def eq[A](a: S[A], b: S[A]): S[Boolean] = infix(LOp.Eq, a, b)
  def add(a: S[BigInt], b: S[BigInt]): S[BigInt] = infix(LOp.Add, a, b)
  def sub(a: S[BigInt], b: S[BigInt]): S[BigInt] = infix(LOp.Sub, a, b)
  def lt(a: S[BigInt], b: S[BigInt]): S[Boolean] = infix(LOp.Lt, a, b)
  def le(a: S[BigInt], b: S[BigInt]): S[Boolean] = infix(LOp.Le, a, b)
  /** A constant, typed (`(2 : Int)`, `([1] : (List Int))`) unless its form says its type (a truth value, a string,
    * a record or a case): Lean would default a numeral to `Nat`, and an empty list to nothing.
    */
  def lit[A](a: A, value: Value, ty: Ty): S[A] = s =>
    val e = constants(value, ty).runA(s.naming).value
    value match
      case Value.Bool(_) | Value.Str(_) | Value.Unit | Value.Data(_, _) => e
      case _                                                           => LExpr.Typed(e, LowerType(ty))
  /** `([] : (List T))`: typed, since nothing around an empty list need say what it holds (`([]).length`). */
  def nil[A](elem: Ty): S[List[A]] = _ => LExpr.Typed(LExpr.ListLit(Nil), LowerType(Ty.ListOf(elem)))
  /** `x :: xs`; onto a literal list, the literal (`[x]`), the element saying what it holds. */
  def cons[A](x: S[A], xs: S[List[A]]): S[List[A]] = s => xs(s) match
    case LExpr.ListLit(es)                   => LExpr.ListLit(x(s) :: es)
    case LExpr.Typed(LExpr.ListLit(Nil), _) => LExpr.ListLit(List(x(s)))
    case other                               => Paren(Infix(LOp.Cons, x(s), other))
  def append[A](xs: S[List[A]], ys: S[List[A]]): S[List[A]] = infix(LOp.Append, xs, ys)
  def length[A](xs: S[List[A]]): S[BigInt] = s => LExpr.Typed(LExpr.Dot(Paren(xs(s)), "length"), name("Int"))
  def all[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = member(xs, x, p)(LExpr.Forall(_, _))
  def any[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = member(xs, x, p)(LExpr.Exists(_, _))
  def filter[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[List[A]] =
    mapped("List.filter", xs, x, p.andThen(_.andThen(decide)))
  def map[A, B](xs: S[List[A]], x: Bound[A])(f: S[A] => S[B]): S[List[B]] = mapped("List.map", xs, x, f)
  def flatMap[A, B](xs: S[List[A]], x: Bound[A])(f: S[A] => S[List[B]]): S[List[B]] = mapped("List.flatMap", xs, x, f)
  def find[A](xs: S[List[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Option[A]] =
    mapped("List.find?", xs, x, p.andThen(_.andThen(decide)))
  def contains[A](xs: S[List[A]], x: S[A]): S[Boolean] = infix(LOp.Mem, x, xs)
  def zip[A, B](xs: S[List[A]], ys: S[List[B]]): S[List[(A, B)]] = s => call(const("List.zip"), List(xs(s), ys(s)))
  def isEmpty[A](xs: S[List[A]]): S[Boolean] = infix(LOp.Eq, xs, _ => LExpr.ListLit(Nil))
  def nodup[A](xs: S[List[A]]): S[Boolean] = s => call(const("List.Nodup"), List(xs(s)))
  def pairwise[A](xs: S[List[A]], x: Bound[A], y: Bound[A])(p: (S[A], S[A]) => S[Boolean]): S[Boolean] = s =>
    val (a, inner) = s.bind(x.hint, x.ty)
    val (b, body) = inner.bind(y.hint, y.ty)
    val fn = LExpr.Fun(List(typed(a, x.ty), typed(b, y.ty)), p(variable(a), variable(b))(body))
    call(const("List.Pairwise"), List(Paren(fn), xs(s)))
  def foldLeft[A, B](xs: S[List[A]], z: S[B], acc: Bound[B], x: Bound[A])(f: (S[B], S[A]) => S[B]): S[B] = s =>
    val (a, inner) = s.bind(acc.hint, acc.ty)
    val (y, body) = inner.bind(x.hint, x.ty)
    val fn = LExpr.Fun(List(typed(a, acc.ty), typed(y, x.ty)), f(variable(a), variable(y))(body))
    call(const("List.foldl"), List(Paren(fn), z(s), xs(s)))
  def some[A](a: S[A]): S[Option[A]] = s => call(name("some"), List(a(s)))
  /** `(none : (Option T))`, typed as the empty list is. */
  def none[A](elem: Ty): S[Option[A]] = _ => LExpr.Typed(name("none"), LowerType(Ty.OptionOf(elem)))
  def foldOption[A, R](o: S[Option[A]], ifNone: S[R], x: Bound[A])(ifSome: S[A] => S[R]): S[R] = s =>
    val (n, body) = bound(x, s, ifSome)
    Paren(LExpr.Match(o(s), List(name("none") -> ifNone(s), LExpr.App(name("some"), List(LExpr.Name(n))) -> body)))
  /** `(∀ (x : T), (o = (some x)) → p)`, as `optionAny` is `(∃ (x : T), (o = (some x)) ∧ p)`. */
  def optionAll[A](o: S[Option[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] =
    holding(o, x, p, LOp.Arrow)(LExpr.Forall(_, _))
  def optionAny[A](o: S[Option[A]], x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] =
    holding(o, x, p, LOp.And)(LExpr.Exists(_, _))
  def isDefined[A](o: S[Option[A]]): S[Boolean] = infix(LOp.Ne, o, _ => name("none"))
  def getOrElse[A](o: S[Option[A]], default: S[A]): S[A] = s => call(const("Option.getD"), List(o(s), default(s)))
  /** `(Except.error e : (Except E A))`: typed by the whole, which one side alone does not say. */
  def left[E, A](e: S[E], ty: Ty): S[Either[E, A]] =
    s => LExpr.Typed(LExpr.App(const("Except.error"), List(e(s))), LowerType(ty))
  def right[E, A](a: S[A], ty: Ty): S[Either[E, A]] =
    s => LExpr.Typed(LExpr.App(const("Except.ok"), List(a(s))), LowerType(ty))
  def foldEither[E, A, R](v: S[Either[E, A]], e: Bound[E], a: Bound[A])(l: S[E] => S[R], r: S[A] => S[R]): S[R] = s =>
    val ((x, onLeft), (y, onRight)) = (bound(e, s, l), bound(a, s, r))
    Paren(LExpr.Match(v(s), List(LExpr.App(const("Except.error"), List(LExpr.Name(x))) -> onLeft,
      LExpr.App(const("Except.ok"), List(LExpr.Name(y))) -> onRight)))
  def forall[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = quantified(x, p)(LExpr.Forall(_, _))
  def exists[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = quantified(x, p)(LExpr.Exists(_, _))
  /** Printed as the `∀` it narrows: Lean states an `always` only as the hypotheses it gives (`Guarded`), what keeps
    * it (`Keeping`), and its witness (`Witnessed`), never as a claim of its own.
    */
  def always[A](x: Bound[A])(p: S[A] => S[Boolean]): S[Boolean] = forall(x)(p)
  /** Lean's model of the world is built on it (the models' instances, the runs one at a time), so it states nothing. */
  def outside(fact: OutsideFact): S[Boolean] = _ => name("True")
  def unchanged(after: S[World], before: S[World]): S[Boolean] = s => Outcomes.unchanged(env, after(s), before(s))
  def construct[F](c: Constructor[F]): S[F] = _ => Atoms.ctor(c.data, c.ctor)
  /** A field of a record made on the spot (`LExpr.Ctor` applied) is its argument, typed by the field. */
  def field[R, F](r: S[R], sel: Selector[R, F]): S[F] = s => r(s) match
    case Paren(LExpr.App(LExpr.Ctor(d, _), args)) if d == Names.ident(sel.record.value) && sel.index < args.size =>
      args(sel.index) match
        case typed: LExpr.Typed => typed
        case arg                => LExpr.Typed(arg, LowerType(sel.ty))
    case other => LExpr.Dot(other, Names.ident(sel.name).text)
  def copy[R, F](r: S[R], sel: Selector[R, F], v: S[F]): S[R] =
    s => LExpr.Update(r(s), List(Names.ident(sel.name) -> v(s)))
  def pair[A, B](a: S[A], b: S[B]): S[(A, B)] = s => LExpr.Tuple(List(a(s), b(s)))
  def cases[V, R](v: S[V], arms: List[When[S, V, ?, R]], ty: Ty): S[R] =
    s => Paren(LExpr.Match(v(s), arms.map(arm(_, s))))
  def lam[A, B](x: Bound[A])(f: S[A] => S[B]): S[A => B] = s =>
    val (n, body) = bound(x, s, f)
    Paren(LExpr.Fun(List(typed(n, x.ty)), body))
  def app[A, B](f: S[A => B], a: S[A]): S[B] = s => applied(f(s), a(s))
  def let[A, B](v: S[A], x: Bound[A])(b: S[A] => S[B]): S[B] = s =>
    val (n, body) = bound(x, s, b)
    Paren(LExpr.Let(n, LowerType(x.ty), v(s), body))
  /** A value's name or what stands for it (a witness given before, R14.6); a define on its open terms so written. */
  def param[A](n: SymbolName, ty: Ty): S[A] = _ => standing.getOrElse(n, LExpr.Name(Names.ident(n.value)))
  def define[F](d: Body[F]): S[F] = _ => Atoms.define(env, d.name, byName.get)
  def free[A](x: Binder): S[A] = s => LExpr.Name(s.named(x))
  def part[V](w: S[World], model: ModelName, ty: Ty): S[V] = s => LExpr.Dot(w(s), env.modelField(model).text)
  /** `(match (runExpiry now before) with | (result, after) => post)`: the run's pair taken apart; of a program that
    * may fail, `| (Except.ok result, after) => post | _ => True`: the post is of the runs that succeed.
    */
  def runs[R](p: S[Program[R]], before: S[World], result: Bound[R], after: Bound[World])(
      post: (S[R], S[World]) => S[Boolean]): S[Boolean] = s =>
    val (r, w, body) = outcome(result, after, post, s)
    val run = applied(p(s), before(s))
    Paren(LExpr.Match(run, outcomes.succeeded(run, r, w, body)))
  /** A failing run's arm, `| (Except.error e, after) => post`, every other run `True`. */
  def fails[R, E](p: S[Program[R]], before: S[World], error: Bound[E], after: Bound[World])(
      post: (S[E], S[World]) => S[Boolean]): S[Boolean] = s =>
    val (e, w, body) = outcome(error, after, post, s)
    Paren(LExpr.Match(applied(p(s), before(s)), outcomes.failed(e, w, body)))
  def noted[A](n: Annotation, t: S[A]): S[A] = t

  private def applied(f: LExpr, a: LExpr): LExpr = LeanTerm.applied(f, a)
  private def decide(body: LExpr): LExpr = LExpr.App(name("decide"), List(body))

  /** `(List.map (fun x => body) xs)`: a list operation of a function of each element. */
  private def mapped[A, B](op: String, xs: S[List[A]], x: Bound[A], f: S[A] => S[B]): S[List[B]] = s =>
    val (n, body) = bound(x, s, f, LExprs.identifiers(xs(s)))
    call(const(op), List(Paren(LExpr.Fun(List(LBinder.Bare(n)), body)), xs(s)))

  private def holding[A](o: S[Option[A]], x: Bound[A], p: S[A] => S[Boolean], op: LOp)(
      make: (List[LBinder], LExpr) => LExpr): S[Boolean] = s =>
    val (n, body) = bound(x, s, p, LExprs.identifiers(o(s)))
    val some = Paren(Infix(LOp.Eq, o(s), call(name("some"), List(LExpr.Name(n)))))
    Paren(make(List(typed(n, x.ty)), Infix(op, some, body)))

  private def outcome[O](o: Bound[O], w: Bound[World], post: (S[O], S[World]) => S[Boolean], s: Scope)
      : (LeanName, LeanName, LExpr) =
    val (a, inner) = s.bind(o.hint, o.ty)
    val (b, body) = inner.bind(w.hint, w.ty)
    (a, b, post(variable(a), variable(b))(body))

  private def infix[A, B, R](op: LOp, a: S[A], b: S[B]): S[R] = s => Paren(Infix(op, a(s), b(s)))
  private def variable[A](n: LeanName): S[A] = _ => LExpr.Name(n)
  private def typed(n: LeanName, ty: Ty): LBinder = LBinder.Explicit(n, LowerType(ty))

  /** The binder's name in this scope, and the body printed in the scope one deeper, its variable that name. */
  private def bound[A, B](x: Bound[A], s: Scope, p: S[A] => S[B], avoid: Set[String] = Set.empty): (LeanName, LExpr) =
    val (n, inner) = s.bind(x.hint, x.ty, avoid)
    (n, p(variable(n))(inner))

  private def member[A](xs: S[List[A]], x: Bound[A], p: S[A] => S[Boolean])(make: (List[LBinder], LExpr) => LExpr)
      : S[Boolean] = s =>
    val (n, body) = bound(x, s, p, LExprs.identifiers(xs(s)))
    Paren(make(List(LBinder.Member(n, xs(s))), body))

  private def quantified[A](x: Bound[A], p: S[A] => S[Boolean])(make: (List[LBinder], LExpr) => LExpr)
      : S[Boolean] = s =>
    val (n, body) = bound(x, s, p)
    Paren(make(List(typed(n, x.ty)), body))

  /** `| Event.Expired at => body`: the case's fields named here, the case itself their constructor. */
  private def arm[V, C, R](w: When[S, V, C, R], s: Scope): (LExpr, LExpr) =
    val (names, inner) = w.c.fields.foldLeft((List.empty[LeanName], s)) { case ((ns, sc), (hint, ty)) =>
      val (n, next) = sc.bind(hint, ty)
      (ns :+ n, next)
    }
    val head = Atoms.ctor(w.c.sum, w.c.ctor)
    val pattern = if names.isEmpty then head else LExpr.App(head, names.map(LExpr.Name(_)))
    (pattern, w.body(_ => if names.isEmpty then head else Paren(pattern))(inner))

object LeanTerm:
  type S[A] = Scope => LExpr

  /** `f` applied to `a`, flattened onto a call in parentheses (`(Rooms.covers b t)`). */
  private[term] def applied(f: LExpr, a: LExpr): LExpr = f match
    case LExpr.Paren(LExpr.App(g, as)) => LExpr.Paren(LExpr.App(g, as :+ a))
    case g                             => Atoms.call(g, List(a))
