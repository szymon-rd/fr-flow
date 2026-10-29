package frflow.proof.terms

import frflow.core.expr.Binder
import frflow.core.name.{ModelName, SymbolName, VarId}
import frflow.core.term.*
import frflow.core.term.interpret.{Forward, Guard}
import frflow.core.ty.Ty

/** A call proven code makes of a Definition given plain Scala (owner §37): its arguments' types, and what it states of
  * them given a rule, on the path to it (`stated`: the rule's guard of each argument it reaches, below each condition
  * and quantifier on the way).
  */
final case class AtCall[T[_]](tys: List[Ty], stated: Guard => T[Boolean])

object AtCall:
  /** A call of these arguments: the rule of each one it reaches, all of them. */
  def of[T[_]](s: Sym[T], args: List[(Ty, T[Any])]): AtCall[T] = AtCall(args.map(_._1), g =>
    args.flatMap((ty, v) => g.of[T, Any](ty, s).map(_(v))).reduceOption(s.and).getOrElse(s.bool(true)))

  /** Each call below a condition. */
  def when[T[_]](s: Sym[T], c: T[Boolean])(calls: List[AtCall[T]]): List[AtCall[T]] =
    calls.map(a => AtCall(a.tys, g => s.implies(c, a.stated(g))))

  /** Each call below a binder, for every value of it (meeting `ctx`, when given): its calls read once on a variable
    * no term binds, for their number and types, then each one under the binder.
    */
  def under[T[_], A](s: Sym[T], x: Bound[A], ctx: Option[T[A] => T[Boolean]])(body: T[A] => List[AtCall[T]])
      : List[AtCall[T]] =
    val probe = body(s.free[A](Binder(VarId.step(Int.MaxValue), x.hint, x.ty)))
    probe.indices.toList.map(j => AtCall(probe(j).tys, g => s.forall(x)(v =>
      ctx.fold(body(v)(j).stated(g))(c => s.implies(c(v), body(v)(j).stated(g))))))

/** A term as `base` reads it, with the calls of plain Scala in it, in order; and, while a Definition given plain Scala
  * is applied one argument at a time, the arguments so far and the types still to come.
  */
final case class Calling[T[_], A](t: T[A], calls: List[AtCall[T]], applying: Option[(List[(Ty, T[Any])], List[Ty])])

/** A term read for the calls it makes of Definitions given plain Scala (`scala`), each variable bound outside it as
  * `env` gives it: every operation reads its operands' calls, in order, a branch's below its condition, a body's
  * below its binder (an element of the list, the option's value, any value).
  */
final class Calls[T[_]](s: Sym[T], scala: Set[SymbolName], env: Map[VarId, T[Any]])
    extends Forward[T, [a] =>> Calling[T, a]]:
  private type C[A] = Calling[T, A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): C[A] = Calling(t, Nil, None)
  protected def bwd[A](u: C[A]): T[A] = u.t

  private def kept[A](t: T[A], parts: C[?]*): C[A] = Calling(t, parts.toList.flatMap(_.calls), None)
  private def plus[A](c: C[A], more: List[AtCall[T]]): C[A] = c.copy(calls = c.calls ++ more)
  private def in[A](xs: C[List[A]]): Option[T[A] => T[Boolean]] = Some(v => s.contains(xs.t, v))
  private def over[A, B](x: Bound[A], ctx: Option[T[A] => T[Boolean]])(p: C[A] => C[B]): List[AtCall[T]] =
    AtCall.under(s, x, ctx)(v => p(fwd(v)).calls)

  override def and(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.and(a.t, b.t), a, b)
  override def or(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.or(a.t, b.t), a, b)
  override def not(a: C[Boolean]): C[Boolean] = kept(s.not(a.t), a)
  override def implies(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.implies(a.t, b.t), a, b)
  override def cond[A](c: C[Boolean], t: C[A], e: C[A]): C[A] = Calling(s.cond(c.t, t.t, e.t),
    c.calls ++ AtCall.when(s, c.t)(t.calls) ++ AtCall.when(s, s.not(c.t))(e.calls), None)
  override def eq[A](a: C[A], b: C[A]): C[Boolean] = kept(s.eq(a.t, b.t), a, b)
  override def add(a: C[BigInt], b: C[BigInt]): C[BigInt] = kept(s.add(a.t, b.t), a, b)
  override def sub(a: C[BigInt], b: C[BigInt]): C[BigInt] = kept(s.sub(a.t, b.t), a, b)
  override def lt(a: C[BigInt], b: C[BigInt]): C[Boolean] = kept(s.lt(a.t, b.t), a, b)
  override def le(a: C[BigInt], b: C[BigInt]): C[Boolean] = kept(s.le(a.t, b.t), a, b)
  override def cons[A](x: C[A], xs: C[List[A]]): C[List[A]] = kept(s.cons(x.t, xs.t), x, xs)
  override def append[A](xs: C[List[A]], ys: C[List[A]]): C[List[A]] = kept(s.append(xs.t, ys.t), xs, ys)
  override def length[A](xs: C[List[A]]): C[BigInt] = kept(s.length(xs.t), xs)
  override def all[A](xs: C[List[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(kept(s.all(xs.t, x)(body(p)), xs), over(x, in(xs))(p))
  override def any[A](xs: C[List[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(kept(s.any(xs.t, x)(body(p)), xs), over(x, in(xs))(p))
  override def filter[A](xs: C[List[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[List[A]] =
    plus(kept(s.filter(xs.t, x)(body(p)), xs), over(x, in(xs))(p))
  override def nodup[A](xs: C[List[A]]): C[Boolean] = kept(s.nodup(xs.t), xs)
  override def pairwise[A](xs: C[List[A]], x: Bound[A], y: Bound[A])(p: (C[A], C[A]) => C[Boolean]): C[Boolean] =
    plus(kept(s.pairwise(xs.t, x, y)((a, b) => p(fwd(a), fwd(b)).t), xs),
      AtCall.under(s, x, in(xs))(a => AtCall.under(s, y, in(xs))(b => p(fwd(a), fwd(b)).calls)))
  override def foldLeft[A, B](xs: C[List[A]], z: C[B], acc: Bound[B], x: Bound[A])(f: (C[B], C[A]) => C[B]): C[B] =
    plus(kept(s.foldLeft(xs.t, z.t, acc, x)((b, a) => f(fwd(b), fwd(a)).t), xs, z),
      AtCall.under(s, acc, None)(b => AtCall.under(s, x, in(xs))(a => f(fwd(b), fwd(a)).calls)))
  override def map[A, B](xs: C[List[A]], x: Bound[A])(f: C[A] => C[B]): C[List[B]] =
    plus(kept(s.map(xs.t, x)(body(f)), xs), over(x, in(xs))(f))
  override def flatMap[A, B](xs: C[List[A]], x: Bound[A])(f: C[A] => C[List[B]]): C[List[B]] =
    plus(kept(s.flatMap(xs.t, x)(body(f)), xs), over(x, in(xs))(f))
  override def find[A](xs: C[List[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[Option[A]] =
    plus(kept(s.find(xs.t, x)(body(p)), xs), over(x, in(xs))(p))
  override def contains[A](xs: C[List[A]], x: C[A]): C[Boolean] = kept(s.contains(xs.t, x.t), xs, x)
  override def zip[A, B](xs: C[List[A]], ys: C[List[B]]): C[List[(A, B)]] = kept(s.zip(xs.t, ys.t), xs, ys)
  override def isEmpty[A](xs: C[List[A]]): C[Boolean] = kept(s.isEmpty(xs.t), xs)
  override def some[A](a: C[A]): C[Option[A]] = kept(s.some(a.t), a)
  override def foldOption[A, R](o: C[Option[A]], ifNone: C[R], x: Bound[A])(ifSome: C[A] => C[R]): C[R] =
    plus(kept(s.foldOption(o.t, ifNone.t, x)(body(ifSome)), o),
      AtCall.when(s, s.not(s.isDefined(o.t)))(ifNone.calls) ++ over(x, Some(v => s.eq(o.t, s.some(v))))(ifSome))
  override def optionAll[A](o: C[Option[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(kept(s.optionAll(o.t, x)(body(p)), o), over(x, Some(v => s.eq(o.t, s.some(v))))(p))
  override def optionAny[A](o: C[Option[A]], x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(kept(s.optionAny(o.t, x)(body(p)), o), over(x, Some(v => s.eq(o.t, s.some(v))))(p))
  override def isDefined[A](o: C[Option[A]]): C[Boolean] = kept(s.isDefined(o.t), o)
  override def getOrElse[A](o: C[Option[A]], default: C[A]): C[A] = kept(s.getOrElse(o.t, default.t), o, default)
  override def get[K, V](m: C[Map[K, V]], k: C[K]): C[Option[V]] = kept(s.get(m.t, k.t), m, k)
  override def getOrElseAt[K, V](m: C[Map[K, V]], k: C[K], default: C[V]): C[V] =
    kept(s.getOrElseAt(m.t, k.t, default.t), m, k, default)
  override def updated[K, V](m: C[Map[K, V]], k: C[K], v: C[V]): C[Map[K, V]] = kept(s.updated(m.t, k.t, v.t), m, k, v)
  override def member[A](set: C[Set[A]], x: C[A]): C[Boolean] = kept(s.member(set.t, x.t), set, x)
  override def incl[A](set: C[Set[A]], x: C[A]): C[Set[A]] = kept(s.incl(set.t, x.t), set, x)
  override def union[A](a: C[Set[A]], b: C[Set[A]]): C[Set[A]] = kept(s.union(a.t, b.t), a, b)
  override def left[E, A](e: C[E], ty: Ty): C[Either[E, A]] = kept(s.left(e.t, ty), e)
  override def right[E, A](a: C[A], ty: Ty): C[Either[E, A]] = kept(s.right(a.t, ty), a)
  override def foldEither[E, A, R](v: C[Either[E, A]], e: Bound[E], a: Bound[A])(l: C[E] => C[R], r: C[A] => C[R])
      : C[R] =
    val ty = Ty.EitherOf(e.ty, a.ty)
    plus(kept(s.foldEither(v.t, e, a)(body(l), body(r)), v), over(e, Some(x => s.eq(v.t, s.left(x, ty))))(l) ++
      over(a, Some(x => s.eq(v.t, s.right(x, ty))))(r))
  override def forall[A](x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(fwd(s.forall(x)(body(p))), over(x, None)(p))
  override def exists[A](x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(fwd(s.exists(x)(body(p))), over(x, None)(p))
  override def always[A](x: Bound[A])(p: C[A] => C[Boolean]): C[Boolean] =
    plus(fwd(s.always(x)(body(p))), over(x, None)(p))
  override def field[R, F](r: C[R], sel: Selector[R, F]): C[F] = kept(s.field(r.t, sel), r)
  override def copy[R, F](r: C[R], sel: Selector[R, F], v: C[F]): C[R] = kept(s.copy(r.t, sel, v.t), r, v)
  override def pair[A, B](a: C[A], b: C[B]): C[(A, B)] = kept(s.pair(a.t, b.t), a, b)
  override def cases[S, R](v: C[S], arms: List[When[C, S, ?, R]], ty: Ty): C[R] =
    plus(kept(super.cases(v, arms, ty).t, v), arms.flatMap(w => arm(w)))
  override def lam[A, B](x: Bound[A])(f: C[A] => C[B]): C[A => B] = plus(fwd(s.lam(x)(body(f))), over(x, None)(f))
  override def let[A, B](v: C[A], x: Bound[A])(b: C[A] => C[B]): C[B] =
    plus(kept(s.let(v.t, x)(body(b)), v), b(fwd(v.t)).calls)
  override def param[A](name: SymbolName, ty: Ty): C[A] = Calling(s.param(name, ty), Nil, (ty, scala(name)) match
    case (Ty.FnOf(ins, _), true) => Some((Nil, ins))
    case _                       => None)
  override def free[A](x: Binder): C[A] = fwd(env.get(x.id).fold(s.free[A](x))(_.asInstanceOf[T[A]]))
  override def part[S](w: C[World], model: ModelName, ty: Ty): C[S] = kept(s.part(w.t, model, ty), w)
  override def runs[R](p: C[Program[R]], before: C[World], result: Bound[R], after: Bound[World])(
      post: (C[R], C[World]) => C[Boolean]): C[Boolean] =
    plus(kept(super.runs(p, before, result, after)(post).t, p, before), AtCall.under(s, result, None)(r =>
      AtCall.under(s, after, None)(w => post(fwd(r), fwd(w)).calls)))
  override def fails[R, E](p: C[Program[R]], before: C[World], error: Bound[E], after: Bound[World])(
      post: (C[E], C[World]) => C[Boolean]): C[Boolean] =
    plus(kept(super.fails(p, before, error, after)(post).t, p, before), AtCall.under(s, error, None)(e =>
      AtCall.under(s, after, None)(w => post(fwd(e), fwd(w)).calls)))
  override def unchanged(after: C[World], before: C[World]): C[Boolean] =
    kept(s.unchanged(after.t, before.t), after, before)
  override def noted[A](n: Annotation, t: C[A]): C[A] = t.copy(t = s.noted(n, t.t))

  /** A Definition given plain Scala applied: a call, once its last argument is given. */
  override def app[A, B](f: C[A => B], a: C[A]): C[B] =
    val (applied, calls) = (s.app(f.t, a.t), f.calls ++ a.calls)
    f.applying match
      case Some((args, ty :: rest)) =>
        val sofar = args :+ (ty -> a.t.asInstanceOf[T[Any]])
        if rest.isEmpty then Calling(applied, calls :+ AtCall.of(s, sofar), None)
        else Calling(applied, calls, Some((sofar, rest)))
      case _                        => Calling(applied, calls, None)

  /** A match arm's calls, for every value of its case. */
  private def arm[S, X, R](w: When[C, S, X, R]): List[AtCall[T]] = over(w.x, None)(w.body)

object Calls:
  /** A term in final form read over `s` for its calls. */
  def of[T[_]](s: Sym[T], scala: Set[SymbolName], env: Map[VarId, T[Any]])(t: Stated[?]): Calling[T, Any] =
    t.run.asInstanceOf[Final[Any]][[a] =>> Calling[T, a]](Calls(s, scala, env))
