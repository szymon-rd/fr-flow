package frflow.core.analysis

import cats.syntax.all.*
import cats.data.NonEmptyList
import frflow.core.name.{NodeId, TypeName}
import frflow.core.spec.Range
import frflow.core.term.{Bound, Final, Selector, Sym, World}
import frflow.core.term.interpret.{AtValue, Guard}
import frflow.core.Theory
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.StateModel

/** The hypotheses every variable of a statement comes with (`Guarded`), one guard per statement of `always`,
  * claimed or assumed: its rule at the variable (`AtValue`). `always[T]` on each value of `T`, each element of a
  * list of them, each one a record's field holds so (`RoomBookings`' bookings), and each one a world's model holds as
  * its state or its state's elements; `always(stored)` on each world. Each guard is built from the variable's `Ty`,
  * so its casts are typed by it. Guards are stated in Lean; Scala checks an `always` where a value is made (`Made`).
  */
object Guards:
  def of(t: Theory): List[Guard] = byAlways(t).map(_._2)

  /** Each statement of `always`, with its guard. */
  def byAlways(t: Theory): List[(NodeId, Guard)] = t.nodes.map(_.node).flatMap(n =>
    (n.statement.said, n.statement.range).tupled.collect {
      case (f, r @ (Range.Made(_) | Range.Reached(_))) =>
        n.id -> guard(f.term, r, Scope.models(t, r), t.vocabulary.dataType)
    })

  /** Whether `always[T]`'s guard applies to a value of `x`: a `T`, a list of them, or a record with such a field. */
  def applies(t: Theory, ty: Ty, x: Ty): Boolean = x == ty || x == Ty.ListOf(ty) || fields(t.vocabulary.dataType,
    ty, x).nonEmpty

  private def guard(rule: Final[Boolean], range: Range, models: List[StateModel],
      data: TypeName => Option[DataType]): Guard = new Guard:
    def of[T[_], A](x: Ty, s: Sym[T]): Option[T[A] => T[Boolean]] =
      val at: T[Any] => T[Boolean] = v => AtValue.of(rule, s, v)
      def on(x: Ty): Option[T[Any] => T[Boolean]] = (range, x) match
        case (Range.Made(ty), _) if x == ty            => Some(at)
        case (Range.Made(ty), _) if x == Ty.ListOf(ty) => Some(each(s, ty, at))
        case (Range.Made(ty), Ty.World)                => inWorld(s, models)(m => whole(s, ty, m, at))
        case (Range.Made(ty), Ty.Data(_))              => NonEmptyList.fromList(fields(data, ty, x)).map(fs => r =>
            fs.map(f => on(f.ty).fold(s.bool(true))(_(s.field(r, f)))).reduceLeft(s.and))
        case (Range.Reached(_), Ty.World)              => Some(at)
        case _                                         => None
      on(x).map(g => (v: T[A]) => g(v.asInstanceOf[T[Any]]))

  /** A record's fields holding a `T` or a list of them, as selectors Lean prints (`r.bookings`); a guard is stated in
    * Lean only, so Scala's getter is never run.
    */
  private def fields(data: TypeName => Option[DataType], ty: Ty, x: Ty): List[Selector[Any, Any]] = x match
    case Ty.Data(n) => data(n).toList.collect { case DataType.Product(_, _, fs) => fs }.flatten.zipWithIndex.collect {
        case (f, i) if f.ty == ty || f.ty == Ty.ListOf(ty) => Selector[Any, Any](f.name, i, n, f.ty, _ => leanOnly,
          (_, _) => leanOnly)
      }
    case _          => Nil

  private def leanOnly: Nothing = throw IllegalStateException("FrFlow bug: a guard read in Scala (Made checks it)")

  /** The rule of a model's state: of the state itself, or of each of its elements. */
  private def whole[T[_]](s: Sym[T], ty: Ty, m: StateModel, at: T[Any] => T[Boolean]): T[Any] => T[Boolean] =
    if m.state == ty then at else each(s, ty, at)

  /** `∀ b ∈ xs, rule b`. */
  private def each[T[_]](s: Sym[T], ty: Ty, rule: T[Any] => T[Boolean]): T[Any] => T[Boolean] =
    xs => s.all(xs.asInstanceOf[T[List[Any]]], Bound(hint(ty), ty))(rule)

  /** `on` each model's state in the world, those whose state it applies to, together. */
  private def inWorld[T[_]](s: Sym[T], models: List[StateModel])(on: StateModel => T[Any] => T[Boolean])
      : Option[T[Any] => T[Boolean]] =
    Option.when(models.nonEmpty)(w =>
      models.map(m => on(m)(s.part[Any](w.asInstanceOf[T[World]], m.name, m.state))).reduce(s.and))

  private def hint(ty: Ty): String = Ty.names(ty).headOption.fold("x")(_.value.take(1).toLowerCase)
