package frflow.core.term.interpret

import frflow.core.expr.*
import frflow.core.name.{ModelName, SymbolName, VarId}
import frflow.core.term.*
import frflow.core.ty.{NumKind, Ty}

/** The initial form of a term (LNCS 7470 §2.4 and §3.3, `initialize`): the IR `Expr` the analyses read (what changed,
  * mentions, the refutation's hint, the layout), each binder named by its depth, the number of binders around it
  * (§3.2's `S` counts the same way). No back end reads it: Lean is printed and Scala evaluated from the term itself.
  * Application is flattened (`app(app(f, a), b)` is `f a b`); a field of a constructor is its argument, so a match
  * arm's case reads its fields as the pattern's variables.
  */
object ToExpr extends Sym[ToExpr.IR]:
  type IR[A] = Int => Expr

  def of[A](t: Final[A], depth: Int = 0): Expr = t[IR](this)(depth)

  def bool(b: Boolean): IR[Boolean] = _ => Expr.Lit(Value.Bool(b), Ty.Bool)
  def and(a: IR[Boolean], b: IR[Boolean]): IR[Boolean] = prim(PrimOp.And, Ty.Bool, a, b)
  def or(a: IR[Boolean], b: IR[Boolean]): IR[Boolean] = prim(PrimOp.Or, Ty.Bool, a, b)
  def not(a: IR[Boolean]): IR[Boolean] = prim(PrimOp.Not, Ty.Bool, a)
  def implies(a: IR[Boolean], b: IR[Boolean]): IR[Boolean] = prim(PrimOp.Implies, Ty.Bool, a, b)
  def cond[A](c: IR[Boolean], ifTrue: IR[A], ifFalse: IR[A]): IR[A] = d => Expr.If(c(d), ifTrue(d), ifFalse(d))
  def eq[A](a: IR[A], b: IR[A]): IR[Boolean] = prim(PrimOp.Eq, Ty.Bool, a, b)
  def add(a: IR[BigInt], b: IR[BigInt]): IR[BigInt] = prim(PrimOp.Add, big, a, b)
  def sub(a: IR[BigInt], b: IR[BigInt]): IR[BigInt] = prim(PrimOp.Sub, big, a, b)
  def lt(a: IR[BigInt], b: IR[BigInt]): IR[Boolean] = prim(PrimOp.Lt, Ty.Bool, a, b)
  def le(a: IR[BigInt], b: IR[BigInt]): IR[Boolean] = prim(PrimOp.Le, Ty.Bool, a, b)
  def lit[A](a: A, value: Value, ty: Ty): IR[A] = _ => Expr.Lit(value, ty)
  def nil[A](elem: Ty): IR[List[A]] = _ => Expr.ListOf(Nil, elem)
  def cons[A](x: IR[A], xs: IR[List[A]]): IR[List[A]] = d => Expr.Prim(PrimOp.Cons, List(x(d), xs(d)), typed(xs, d))
  def append[A](xs: IR[List[A]], ys: IR[List[A]]): IR[List[A]] =
    d => Expr.Prim(PrimOp.Append, List(xs(d), ys(d)), typed(xs, d))
  def length[A](xs: IR[List[A]]): IR[BigInt] = prim(PrimOp.Length, big, xs)
  def all[A](xs: IR[List[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] =
    iterate(Iteration.Forall, xs, x, p)((_, _) => Ty.Bool)
  def any[A](xs: IR[List[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] =
    iterate(Iteration.Exists, xs, x, p)((_, _) => Ty.Bool)
  def filter[A](xs: IR[List[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[List[A]] =
    iterate(Iteration.Filter, xs, x, p)((t, _) => t)
  def map[A, B](xs: IR[List[A]], x: Bound[A])(f: IR[A] => IR[B]): IR[List[B]] =
    iterate(Iteration.Map, xs, x, f)((_, b) => Ty.ListOf(b))
  def flatMap[A, B](xs: IR[List[A]], x: Bound[A])(f: IR[A] => IR[List[B]]): IR[List[B]] =
    iterate(Iteration.FlatMap, xs, x, f)((_, b) => b)
  def find[A](xs: IR[List[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Option[A]] =
    iterate(Iteration.Find, xs, x, p)((_, _) => Ty.OptionOf(x.ty))
  def contains[A](xs: IR[List[A]], x: IR[A]): IR[Boolean] = prim(PrimOp.Contains, Ty.Bool, xs, x)
  def zip[A, B](xs: IR[List[A]], ys: IR[List[B]]): IR[List[(A, B)]] = d =>
    val (a, b) = (xs(d), ys(d))
    Expr.Prim(PrimOp.Zip, List(a, b), Ty.ListOf(Ty.TupleOf(List(a, b).map(e => element(Exprs.typeOf(e))))))
  def isEmpty[A](xs: IR[List[A]]): IR[Boolean] = prim(PrimOp.IsEmpty, Ty.Bool, xs)
  def nodup[A](xs: IR[List[A]]): IR[Boolean] = prim(PrimOp.Nodup, Ty.Bool, xs)
  def pairwise[A](xs: IR[List[A]], x: Bound[A], y: Bound[A])(p: (IR[A], IR[A]) => IR[Boolean]): IR[Boolean] = d =>
    val (a, b) = (binder(x, d), binder(y, d + 1))
    Expr.Pairwise(xs(d), a, b, p(variable(a), variable(b))(d + 2))
  def foldLeft[A, B](xs: IR[List[A]], z: IR[B], acc: Bound[B], x: Bound[A])(f: (IR[B], IR[A]) => IR[B]): IR[B] = d =>
    val (a, y) = (binder(acc, d), binder(x, d + 1))
    Expr.Fold(xs(d), z(d), a, y, f(variable(a), variable(y))(d + 2))
  def some[A](a: IR[A]): IR[Option[A]] = d => Expr.SomeOf(a(d))
  def none[A](elem: Ty): IR[Option[A]] = _ => Expr.Lit(Value.Maybe(None), Ty.OptionOf(elem))
  def foldOption[A, R](o: IR[Option[A]], ifNone: IR[R], x: Bound[A])(ifSome: IR[A] => IR[R]): IR[R] = d =>
    val (y, none) = (binder(x, d), ifNone(d))
    Expr.Match(o(d), List(Arm(Pattern.NoneP, none), Arm(Pattern.SomeP(y), ifSome(variable(y))(d + 1))),
      Exprs.typeOf(none))
  def optionAll[A](o: IR[Option[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] =
    iterate(Iteration.Forall, o, x, p)((_, _) => Ty.Bool)
  def optionAny[A](o: IR[Option[A]], x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] =
    iterate(Iteration.Exists, o, x, p)((_, _) => Ty.Bool)
  def isDefined[A](o: IR[Option[A]]): IR[Boolean] = prim(PrimOp.NonEmpty, Ty.Bool, o)
  def getOrElse[A](o: IR[Option[A]], default: IR[A]): IR[A] =
    d => Expr.Prim(PrimOp.GetOrElse, List(o(d), default(d)), typed(default, d))
  def get[K, V](m: IR[Map[K, V]], k: IR[K]): IR[Option[V]] = d =>
    val at = m(d)
    Expr.Prim(PrimOp.Get, List(at, k(d)), Ty.OptionOf(valueOf(Exprs.typeOf(at))))
  def getOrElseAt[K, V](m: IR[Map[K, V]], k: IR[K], default: IR[V]): IR[V] =
    d => Expr.Prim(PrimOp.GetOrElseAt, List(m(d), k(d), default(d)), typed(default, d))
  def updated[K, V](m: IR[Map[K, V]], k: IR[K], v: IR[V]): IR[Map[K, V]] = d => alike(PrimOp.Updated, m(d), k(d), v(d))
  def member[A](s: IR[Set[A]], x: IR[A]): IR[Boolean] = prim(PrimOp.Contains, Ty.Bool, s, x)
  def incl[A](s: IR[Set[A]], x: IR[A]): IR[Set[A]] = d => alike(PrimOp.Incl, s(d), x(d))
  def union[A](s: IR[Set[A]], t: IR[Set[A]]): IR[Set[A]] = d => alike(PrimOp.Union, s(d), t(d))
  def left[E, A](e: IR[E], ty: Ty): IR[Either[E, A]] = d => Expr.Inject(Side.Error, e(d), ty)
  def right[E, A](a: IR[A], ty: Ty): IR[Either[E, A]] = d => Expr.Inject(Side.Value, a(d), ty)
  def foldEither[E, A, R](v: IR[Either[E, A]], e: Bound[E], a: Bound[A])(l: IR[E] => IR[R], r: IR[A] => IR[R])
      : IR[R] = d =>
    val (x, y) = (binder(e, d), binder(a, d))
    val (onLeft, onRight) = (l(variable(x))(d + 1), r(variable(y))(d + 1))
    Expr.Match(v(d), List(Arm(Pattern.Outcome(Side.Error, x), onLeft), Arm(Pattern.Outcome(Side.Value, y), onRight)),
      Exprs.typeOf(onLeft))
  def forall[A](x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] = quant(Quantifier.Forall, x, p)
  def exists[A](x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] = quant(Quantifier.Exists, x, p)
  def always[A](x: Bound[A])(p: IR[A] => IR[Boolean]): IR[Boolean] = quant(Quantifier.Always, x, p)
  def construct[F](c: Constructor[F]): IR[F] = _ => Expr.Make(c.data, c.ctor, Nil)
  def field[R, F](r: IR[R], s: Selector[R, F]): IR[F] = d => r(d) match
    case Expr.Make(_, _, args) if s.index < args.size => args(s.index)
    case other                                       => Expr.Field(other, s.record, s.index, s.ty)
  def copy[R, F](r: IR[R], s: Selector[R, F], v: IR[F]): IR[R] = d => Expr.Copy(r(d), s.record, List(s.index -> v(d)))
  def pair[A, B](a: IR[A], b: IR[B]): IR[(A, B)] = d => Expr.Tuple(List(a(d), b(d)))
  def cases[S, R](s: IR[S], arms: List[When[IR, S, ?, R]], ty: Ty): IR[R] =
    d => Expr.Match(s(d), arms.map(arm(_, d)), ty)
  def lam[A, B](x: Bound[A])(f: IR[A] => IR[B]): IR[A => B] = d =>
    val (y, body) = (binder(x, d), f(variable(binder(x, d)))(d + 1))
    Expr.Fun(Lambda(List(y), body, Exprs.typeOf(body)))
  def app[A, B](f: IR[A => B], a: IR[A]): IR[B] = d => f(d) match
    case Expr.Call(n, as, t)  => Expr.Call(n, as :+ a(d), Ty.applied(t))
    case Expr.Apply(g, as, t) => Expr.Apply(g, as :+ a(d), Ty.applied(t))
    case Expr.Make(n, c, as)  => Expr.Make(n, c, as :+ a(d))
    case g                    => Expr.Apply(g, List(a(d)), Ty.applied(Exprs.typeOf(g)))
  def let[A, B](v: IR[A], x: Bound[A])(body: IR[A] => IR[B]): IR[B] = d =>
    Expr.Let(binder(x, d), v(d), body(variable(binder(x, d)))(d + 1))
  def param[A](name: SymbolName, ty: Ty): IR[A] = _ => Expr.Sym(name, ty)
  def define[F](df: Body[F]): IR[F] = _ => Expr.Call(df.name, Nil, df.ty)
  def free[A](x: Binder): IR[A] = _ => Expr.Var(x)
  def part[S](w: IR[World], model: ModelName, ty: Ty): IR[S] = d => Expr.Part(w(d), model, ty)
  def outside(fact: OutsideFact): IR[Boolean] = _ => Expr.Outside(fact)
  def runs[R](p: IR[Program[R]], before: IR[World], result: Bound[R], after: Bound[World])(
      post: (IR[R], IR[World]) => IR[Boolean]): IR[Boolean] = run(false, result, after)(p, before)(post)
  def fails[R, E](p: IR[Program[R]], before: IR[World], error: Bound[E], after: Bound[World])(
      post: (IR[E], IR[World]) => IR[Boolean]): IR[Boolean] = run(true, error, after)(p, before)(post)
  def noted[A](n: Annotation, t: IR[A]): IR[A] = t

  private val big = Ty.Num(NumKind.Big)
  private def prim[A](op: PrimOp, ty: Ty, args: IR[?]*): IR[A] = d => Expr.Prim(op, args.toList.map(_(d)), ty)
  private def typed(xs: IR[?], d: Int): Ty = Exprs.typeOf(xs(d))
  private def element(t: Ty): Ty = Ty.elementOf(t).getOrElse(t)
  private def valueOf(t: Ty): Ty = t match
    case Ty.MapOf(_, v) => v
    case other          => other
  /** An operation typed as its first operand (a map updated is a map of its type). */
  private def alike(op: PrimOp, first: Expr, rest: Expr*): Expr =
    Expr.Prim(op, first :: rest.toList, Exprs.typeOf(first))
  private def binder(x: Bound[?], d: Int): Binder = Binder(VarId.level(d), x.hint, x.ty)
  private def variable[A](x: Binder): IR[A] = _ => Expr.Var(x)

  /** An arm: the case's fields bound from `d`, the case itself their constructor (so a field read is its variable). */
  private def arm[S, C, R](a: When[IR, S, C, R], d: Int): Arm =
    val fields = a.c.fields.zipWithIndex.map { case ((hint, ty), i) => Binder(VarId.level(d + i), hint, ty) }
    val whole: IR[C] = _ => Expr.Make(a.c.sum, a.c.ctor, fields.map(Expr.Var(_)))
    Arm(Pattern.Ctor(a.c.sum, a.c.ctor, fields), a.body(whole)(d + fields.size))

  private def run[O](failing: Boolean, outcome: Bound[O], after: Bound[World])(p: IR[?], before: IR[World])(
      post: (IR[O], IR[World]) => IR[Boolean]): IR[Boolean] = d =>
    val (o, w) = (binder(outcome, d), binder(after, d + 1))
    Expr.Runs(p(d), before(d), failing, o, w, post(variable(o), variable(w))(d + 2))

  /** A body over a list's or an option's elements, typed from the receiver's type and the body's. */
  private def iterate[A, B, R](how: Iteration, xs: IR[?], x: Bound[A], p: IR[A] => IR[B])(ty: (Ty, Ty) => Ty): IR[R] =
    d =>
      val (y, on) = (binder(x, d), xs(d))
      val body = p(variable(y))(d + 1)
      Expr.Iterate(how, on, y, body, ty(Exprs.typeOf(on), Exprs.typeOf(body)))

  private def quant[A](q: Quantifier, x: Bound[A], p: IR[A] => IR[Boolean]): IR[Boolean] = d =>
    Expr.Quant(q, List(binder(x, d)), p(variable(binder(x, d)))(d + 1))
