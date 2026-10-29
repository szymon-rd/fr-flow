package frflow.core.expr

import frflow.core.name.SymbolName
import frflow.core.term.*
import frflow.core.term.interpret.Forward

/** A term with its binders' hints and its symbols renamed, the same term otherwise: what the printer's capture laws
  * run the generated terms through, so every binder is named as Lean's keywords and prelude names, their mangled
  * forms, the laws' types, models and FrModel, and the symbols themselves (raw and as Lean spells them). A hint's new
  * name depends on the hint and the seed only, so every interpreter sees the same term.
  */
final class Renamed[T[_]](protected val base: Sym[T], hint: String => String, symbol: SymbolName => SymbolName)
    extends Forward[T, T]:
  protected def fwd[A](t: T[A]): T[A] = t
  protected def bwd[A](u: T[A]): T[A] = u
  private def b[A](x: Bound[A]): Bound[A] = x.copy(hint = hint(x.hint))

  override def all[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] = base.all(xs, b(x))(p)
  override def any[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] = base.any(xs, b(x))(p)
  override def filter[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[List[A]] = base.filter(xs, b(x))(p)
  override def pairwise[A](xs: T[List[A]], x: Bound[A], y: Bound[A])(p: (T[A], T[A]) => T[Boolean]): T[Boolean] =
    base.pairwise(xs, b(x), b(y))(p)
  override def foldLeft[A, B](xs: T[List[A]], z: T[B], acc: Bound[B], x: Bound[A])(f: (T[B], T[A]) => T[B]): T[B] =
    base.foldLeft(xs, z, b(acc), b(x))(f)
  override def map[A, B](xs: T[List[A]], x: Bound[A])(f: T[A] => T[B]): T[List[B]] = base.map(xs, b(x))(f)
  override def flatMap[A, B](xs: T[List[A]], x: Bound[A])(f: T[A] => T[List[B]]): T[List[B]] =
    base.flatMap(xs, b(x))(f)
  override def find[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Option[A]] = base.find(xs, b(x))(p)
  override def foldOption[A, R](o: T[Option[A]], ifNone: T[R], x: Bound[A])(ifSome: T[A] => T[R]): T[R] =
    base.foldOption(o, ifNone, b(x))(ifSome)
  override def optionAll[A](o: T[Option[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] =
    base.optionAll(o, b(x))(p)
  override def optionAny[A](o: T[Option[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] =
    base.optionAny(o, b(x))(p)
  override def foldEither[E, A, R](v: T[Either[E, A]], e: Bound[E], a: Bound[A])(l: T[E] => T[R], r: T[A] => T[R])
      : T[R] = base.foldEither(v, b(e), b(a))(l, r)
  override def forall[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] = base.forall(b(x))(p)
  override def exists[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] = base.exists(b(x))(p)
  override def always[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] = base.always(b(x))(p)
  override def cases[S, R](s: T[S], arms: List[When[T, S, ?, R]], ty: frflow.core.ty.Ty): T[R] =
    base.cases(s, arms.map(w => w.copy(c = w.c.copy(fields = w.c.fields.map((h, t) => hint(h) -> t)), x = b(w.x))), ty)
  override def lam[A, B](x: Bound[A])(f: T[A] => T[B]): T[A => B] = base.lam(b(x))(f)
  override def let[A, B](v: T[A], x: Bound[A])(f: T[A] => T[B]): T[B] = base.let(v, b(x))(f)
  override def param[A](name: SymbolName, ty: frflow.core.ty.Ty): T[A] = base.param(symbol(name), ty)
  override def runs[R](p: T[Program[R]], before: T[World], result: Bound[R], after: Bound[World])(
      post: (T[R], T[World]) => T[Boolean]): T[Boolean] = base.runs(p, before, b(result), b(after))(post)
  override def fails[R, E](p: T[Program[R]], before: T[World], error: Bound[E], after: Bound[World])(
      post: (T[E], T[World]) => T[Boolean]): T[Boolean] = base.fails(p, before, b(error), b(after))(post)

object Renamed:
  /** Lean's keywords and prelude names, their mangled forms, the laws' types, models, fields and FrModel, and names a
    * Scala lambda gives (`x$1`).
    */
  val pool: Vector[String] = Vector("by", "at", "fun", "end", "match", "λ", "some", "none", "id", "max", "List", "True",
    "decide", "some_", "some__", "x", "x_1", "x_2", "by_1", "id_", "a_b", "a$b", "__x", "x_x", "n", "n_1", "Booking",
    "Event", "stored", "Laws", "World", "Prop", "Int", "positive", "room", "start", "Except", "pure", "x$1", "_$1",
    "max_", "k", "xs", "slot")

  /** The laws' symbols renamed, each to a name a binder may also be given (`k` is `some`, whose Lean is `some_`). */
  val symbols: Map[String, String] = Map("p" -> "x_1", "k" -> "some", "xs" -> "by", "o" -> "id", "slot" -> "a$b",
    "s" -> "a_b", "m" -> "max", "ev" -> "__x", "outcome" -> "x_x", "run" -> "some_", "attempt" -> "id_")

  def of[A](t: Final[A], seed: Long): Final[A] = renamed(t, seed, s => symbols.get(s.value).fold(s)(SymbolName(_)))

  /** The binders renamed only: a closed term's programs keep the names Lean and Scala hold them by. */
  def binders[A](t: Final[A], seed: Long): Final[A] = renamed(t, seed, identity)

  private def renamed[A](t: Final[A], seed: Long, symbol: SymbolName => SymbolName): Final[A] =
    val hint = (h: String) => pool(Math.floorMod((h.hashCode.toLong * 31 + seed).hashCode, pool.size))
    [T[_]] => (s: Sym[T]) => t[T](Renamed[T](s, hint, symbol))
