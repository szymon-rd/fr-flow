package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.name.{NodeId, TypeName}
import frflow.core.spec.Range
import frflow.core.term.{Bound, Case, Final, Selector, Sym, When, World}
import frflow.core.term.interpret.{AtValue, Guard}
import frflow.core.Theory
import frflow.core.ty.{DataType, Field, Ty}
import frflow.core.vocab.StateModel

/** The hypotheses every variable of a statement comes with (`Guarded`), one guard per statement of `always`,
  * claimed or assumed: its rule at the variable (`AtValue`). `always[T]` on each `T` a value holds: the value
  * itself, each element of a list, an option's value, either side of an `Either`, each component of a tuple, each
  * field of a record or of an enum's case (`RoomBookings`' bookings), and each one a world's model holds in its state
  * (not yet a map's, a set's or a function value's: `Unreached` refuses those); `always(stored)` on each world.
  * Each guard is built from the variable's `Ty`, so its casts are typed by it. Guards are stated in Lean; Scala
  * checks an `always` where a value is made (`Made`).
  */
object Guards:
  def of(t: Theory): List[Guard] = byAlways(t).map(_._2)

  /** Each statement of `always`, with its guard. */
  def byAlways(t: Theory): List[(NodeId, Guard)] = t.nodes.map(_.node).flatMap(n =>
    (n.statement.said, n.statement.range).tupled.collect {
      case (f, r @ (Range.Made(_) | Range.Reached(_))) =>
        n.id -> guard(f.term, r, Scope.models(t, r), t.vocabulary.dataType)
    })

  /** Whether `always[T]`'s guard applies to a value of `x`: `x` holds a `T` where a guard reaches (above). */
  def applies(t: Theory, ty: Ty, x: Ty): Boolean = reaches(t.vocabulary.dataType, ty, Set.empty)(x)

  private def reaches(data: TypeName => Option[DataType], ty: Ty, seen: Set[TypeName])(x: Ty): Boolean =
    x == ty || (x match
      case Ty.ListOf(a)           => reaches(data, ty, seen)(a)
      case Ty.OptionOf(a)         => reaches(data, ty, seen)(a)
      case Ty.EitherOf(e, a)      => List(e, a).exists(reaches(data, ty, seen))
      case Ty.TupleOf(as)         => as.exists(reaches(data, ty, seen))
      case Ty.Data(n) if !seen(n) => data(n).exists(_.fieldTypes.exists(reaches(data, ty, seen + n)))
      case _                      => false)

  private def guard(rule: Final[Boolean], range: Range, models: List[StateModel],
      data: TypeName => Option[DataType]): Guard = new Guard:
    def of[T[_], A](x: Ty, s: Sym[T]): Option[T[A] => T[Boolean]] =
      val at: T[Any] => T[Boolean] = v => AtValue.of(rule, s, v)
      val g = (range, x) match
        case (Range.Made(ty), Ty.World)    =>
          inWorld(s, models.flatMap(m => Within(s, data, ty, at)(m.state, Set.empty).map(m -> _)))
        case (Range.Made(ty), _)           => Within(s, data, ty, at)(x, Set.empty)
        case (Range.Reached(_), Ty.World)  => Some(at)
        case _                             => None
      g.map(g => (v: T[A]) => g(v.asInstanceOf[T[Any]]))

  /** The rule at each `T` a value of a type holds, if it holds one (`reaches`): `∀ b ∈ xs`, a `match` on an option,
    * an `Either` or an enum, a field or a pair's component (`p.1`). A guard is stated in Lean only, so Scala's
    * getters and case tests are never run.
    */
  private final case class Within[T[_]](s: Sym[T], data: TypeName => Option[DataType], ty: Ty,
      at: T[Any] => T[Boolean]):
    private type G = T[Any] => T[Boolean]

    def apply(x: Ty, seen: Set[TypeName]): Option[G] =
      def in(y: Ty) = apply(y, seen)
      if x == ty then Some(at)
      else x match
        case Ty.ListOf(a)           => in(a).map(g => xs => s.all(xs.asInstanceOf[T[List[Any]]], bound(a))(g))
        case Ty.OptionOf(a)         => in(a).map(g => o =>
            s.foldOption(o.asInstanceOf[T[Option[Any]]], s.bool(true), bound(a))(g))
        case Ty.EitherOf(e, a)      => Option.when(in(e).isDefined || in(a).isDefined)(v =>
            s.foldEither(v.asInstanceOf[T[Either[Any, Any]]], bound(e), bound(a))(orTrue(in(e)), orTrue(in(a))))
        case Ty.TupleOf(as)         => all(as.zipWithIndex.flatMap((a, i) =>
            in(a).map(g => (p: T[Any]) => g(s.field(p, component(as.size, i, a))))))
        case Ty.Data(n) if !seen(n) => data(n).flatMap(record(_, seen + n))
        case _                      => None

    /** Each field of a record holding a `T`; of an enum, each case's, in Lean's `match` on it. */
    private def record(d: DataType, seen: Set[TypeName]): Option[G] =
      def holding(fs: List[Field]) = fs.exists(f => apply(f.ty, seen).isDefined)
      def fields(r: T[Any], fs: List[Field]) = fs.zipWithIndex.flatMap((f, i) => apply(f.ty, seen).map(_(
        s.field(r, Selector[Any, Any](f.name, i, d.typeName, f.ty, _ => leanOnly, (_, _) => leanOnly)))))
      d match
        case DataType.Product(_, _, fs) => Option.when(holding(fs))(r => fields(r, fs).reduceLeft(s.and))
        case DataType.Sum(n, _, cs)     => Option.when(cs.exists(c => holding(c.fields)))(v =>
            s.cases[Any, Boolean](v, cs.toList.map(c => When[T, Any, Any, Boolean](
              Case(n, c.name, c.fields.map(f => f.name -> f.ty), _ => leanOnly), bound(Ty.Data(n)),
              r => fields(r, c.fields).reduceLeftOption(s.and).getOrElse(s.bool(true)))), Ty.Bool))

    private def orTrue(g: Option[G]): G = g.getOrElse(_ => s.bool(true))
    private def all(gs: List[G]): Option[G] = Option.when(gs.nonEmpty)(v => gs.map(_(v)).reduceLeft(s.and))
    private def bound(a: Ty): Bound[Any] = Bound(hint(a), a)

  /** Component `i` of a tuple of `n`, as Lean projects it from its nested pairs (`p.1`, `p.2.1`, `p.2.2`). */
  private def component(n: Int, i: Int, ty: Ty): Selector[Any, Any] =
    val path = List.fill(i)("2") ++ Option.when(i < n - 1)("1")
    Selector[Any, Any](path.mkString("."), i, TypeName("Prod"), ty, _ => leanOnly, (_, _) => leanOnly)

  private def leanOnly: Nothing = throw IllegalStateException("FrFlow bug: a guard read in Scala (Made checks it)")

  /** The rule within each model's state in the world, those whose state holds a `T`, together. */
  private def inWorld[T[_]](s: Sym[T], models: List[(StateModel, T[Any] => T[Boolean])])
      : Option[T[Any] => T[Boolean]] =
    Option.when(models.nonEmpty)(w =>
      models.map((m, g) => g(s.part[Any](w.asInstanceOf[T[World]], m.name, m.state))).reduce(s.and))

  private def hint(ty: Ty): String = Ty.names(ty).headOption.fold("x")(_.value.take(1).toLowerCase)
