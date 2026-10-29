package frflow.proof.terms

import frflow.core.expr.Binder
import frflow.core.name.{DefName, ModelName, SymbolName, VarId}
import frflow.core.spec.Form
import frflow.core.term.*
import frflow.core.term.interpret.Forward
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** A term read for the calls it makes of Definitions given plain Scala, each variable bound outside it as `env` gives
  * it: every operation reads its operands' calls, in order, a branch's below its condition, a body's below its binder
  * (an element of the list, the option's value, any value, no rule assumed of it). A Definition whose proven code is a
  * define, and a define written on the spot, are read in place on the arguments they are given (`covered.proven`,
  * `define`), so what proven code hands on through them is checked where it reaches plain Scala; `inlining` holds the
  * defines being read, each read once on a path.
  */
final class Calls[T[_]](s: Sym[T], covered: Covered, env: Map[VarId, T[Any]], inlining: Set[DefName])
    extends Forward[T, [a] =>> Calling[T, a]]:
  private type C[A] = Calling[T, A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): C[A] = Calling.of(t, Nil)
  protected def bwd[A](u: C[A]): T[A] = u.t

  private def kept[A](t: T[A], parts: C[?]*): C[A] = Calling.of(t, parts.toList.flatMap(_.calls))
  private def plus[A](c: C[A], more: List[AtCall[T]]): C[A] = c.copy(calls = c.calls ++ more)
  private def in[A](xs: C[List[A]]): Option[T[A] => T[Boolean]] = Some(v => s.contains(xs.t, v))
  private def over[A, B](x: Bound[A], ctx: Option[T[A] => T[Boolean]])(p: C[A] => C[B]): List[AtCall[T]] =
    AtCall.under(s, x, ctx)(v => p(fwd(v)).calls)

  override def and(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.and(a.t, b.t), a, b)
  override def or(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.or(a.t, b.t), a, b)
  override def not(a: C[Boolean]): C[Boolean] = kept(s.not(a.t), a)
  override def implies(a: C[Boolean], b: C[Boolean]): C[Boolean] = kept(s.implies(a.t, b.t), a, b)
  override def cond[A](c: C[Boolean], t: C[A], e: C[A]): C[A] = Calling.of(s.cond(c.t, t.t, e.t),
    c.calls ++ AtCall.when(s, c.t)(t.calls) ++ AtCall.when(s, s.not(c.t))(e.calls))
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
  /** A lambda: its calls for every value of its input, and its body, read on what it is applied to. */
  override def lam[A, B](x: Bound[A])(f: C[A] => C[B]): C[A => B] =
    // A term of `A` is one of `Any` to every interpreter: the type parameter is Scala's only.
    Calling(s.lam(x)(body(f)), over(x, None)(f), None, Some(a => f(a.asInstanceOf[C[A]]).asInstanceOf[C[Any]]))
  override def let[A, B](v: C[A], x: Bound[A])(b: C[A] => C[B]): C[B] =
    plus(kept(s.let(v.t, x)(body(b)), v), b(v.copy(calls = Nil)).calls)
  /** A define written on the spot: its body, read on its arguments where it is applied. */
  override def define[F](d: Body[F]): C[F] =
    if inlining(d.name) then fwd(s.define(d))
    else Calling(s.define(d), Nil, None, d.body[[a] =>> Calling[T, a]](Calls(s, covered, Map.empty, inlining + d.name))
      .body)
  /** A Definition given plain Scala, or whose proven code is a define, about to be applied. */
  override def param[A](name: SymbolName, ty: Ty): C[A] = Calling(s.param(name, ty), Nil, ty match
    case Ty.FnOf(ins, _) if covered.scala(name) => Some(Calling.Pending(None, Nil, ins))
    case Ty.FnOf(ins, _)                       => covered.proven.get(name).filterNot(d => inlining(d.name))
        .map(d => Calling.Pending(Some(d), Nil, ins))
    case _                                     => None, None)
  // `env` holds the value the binder was bound to, of its type `A`.
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

  /** Once its last argument is given: a Definition given plain Scala, a call; one whose proven code is a define, its
    * code's calls on these arguments. A lambda applied: its body's calls on the argument.
    */
  override def app[A, B](f: C[A => B], a: C[A]): C[B] =
    val applied = s.app(f.t, a.t)
    (f.pending, f.body) match
      case (Some(Calling.Pending(proven, args, ty :: rest)), _) =>
        val sofar = args :+ (ty -> widen(a.t))
        if rest.nonEmpty then Calling(applied, f.calls ++ a.calls, Some(Calling.Pending(proven, sofar, rest)), None)
        else Calling.of(applied, f.calls ++ a.calls ++ proven.fold(List(AtCall.of(s, sofar)))(inlined(_, sofar)))
      case (_, Some(h))                                         =>
        val r = h(a.copy(t = widen(a.t)))
        Calling(applied, a.calls ++ r.calls, r.pending, r.body)
      case _                                                    => Calling.of(applied, f.calls ++ a.calls)

  /** A define's calls, its inputs bound to the arguments. */
  private def inlined(d: Define, args: List[(Ty, T[Any])]): List[AtCall[T]] = d.written.form match
    case Form.Term(term) => Calls.of(s, covered, d.lambda.params.map(_.id).zip(args.map(_._2)).toMap,
        inlining + d.name)(term).calls
    case Form.Steps(_)   => Nil

  // A term of `A` is one of `Any` to every interpreter: the type parameter is Scala's only.
  private def widen[A](t: T[A]): T[Any] = t.asInstanceOf[T[Any]]

  /** A match arm's calls, for every value of its case. */
  private def arm[S, X, R](w: When[C, S, X, R]): List[AtCall[T]] = over(w.x, None)(w.body)

object Calls:
  /** A term in final form read over `s` for its calls. */
  def of[T[_]](s: Sym[T], covered: Covered, env: Map[VarId, T[Any]], inlining: Set[DefName] = Set.empty)(
      t: Stated[?]): Calling[T, Any] =
    // A stated term's `run` is a term of its own type, whatever that is: read as one of `Any`.
    t.run.asInstanceOf[Final[Any]][[a] =>> Calling[T, a]](Calls(s, covered, env, inlining))
