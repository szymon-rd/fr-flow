package frflow.dsl.compiled

import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.lifted.steps.Among
import frflow.dsl.structure.ReadPorts
import frflow.dsl.term.Term as DTerm

/** A term taken at the type an operation needs it at. What a Scala tree is, its type says, and that type is no
  * Scala type here: the compiler holds every term as a term of anything. Where an operation needs a truth value, a
  * number, a list, the term is asked what it was compiled as (`rocqType.ty`), and one compiled as anything else is
  * refused where it is read, with its place. These are the compiler's casts of terms: each after its check, and no
  * other part of the compiler casts one.
  */
private[compiled] trait Readings extends ReadPorts:
  import q.reflect.*

  /** A term, nothing asked of it. */
  def any(t: DTerm[?]): DTerm[Any] = t.asInstanceOf[DTerm[Any]] // nothing is taken of what it is of

  /** `t` as an `A`, if it was compiled as what `is` takes: refused at `at`, or, of a term the compiler made
    * itself (no place), a bug of the compiler's.
    */
  private def taken[A](t: DTerm[?], what: String, at: Option[Tree])(is: PartialFunction[Ty, Unit]): DTerm[A] =
    if is.isDefinedAt(t.rocqType.ty) then t.asInstanceOf[DTerm[A]] // its own type was asked, just above
    else at.fold(throw IllegalStateException(s"FrFlow bug: $what read of a ${t.rocqType.ty}"))(
      refuse(s"a value used as $what, which is compiled as a ${t.rocqType.ty}", _))

  def asTruth(t: DTerm[?], at: Tree): DTerm[Boolean] = taken(t, "a truth value", Some(at)) { case Ty.Bool => }
  def asNumber(t: DTerm[?], at: Tree): DTerm[BigInt] =
    taken(t, "a number", Some(at)) { case Ty.Num(NumKind.Big) => }
  def asList(t: DTerm[?], at: Tree): DTerm[List[Any]] = taken(t, "a list", Some(at)) { case Ty.ListOf(_) => }
  def asOption(t: DTerm[?], at: Tree): DTerm[Option[Any]] =
    taken(t, "an option", Some(at)) { case Ty.OptionOf(_) => }
  def asMap(t: DTerm[?], at: Tree): DTerm[Map[Any, Any]] = taken(t, "a map", Some(at)) { case Ty.MapOf(_, _) => }
  def asSet(t: DTerm[?], at: Tree): DTerm[Set[Any]] = taken(t, "a set", Some(at)) { case Ty.SetOf(_) => }
  def asPair(t: DTerm[?], at: Tree): DTerm[(Any, Any)] =
    taken(t, "a pair", Some(at)) { case Ty.TupleOf(List(_, _)) => }

  /** What the compiler makes itself: a constructor taking its fields, and, while it reads Scala that changes
    * state, a result with the state after it, the traces of a call's steps, the schedule of the other calls.
    */
  def madeFunction(t: DTerm[?]): DTerm[Any => Any] = taken(t, "a function", None) { case Ty.FnOf(_, _) => }
  def madePair(t: DTerm[?]): DTerm[(Any, Any)] = taken(t, "a pair", None) { case Ty.TupleOf(List(_, _)) => }
  def madeTraces(t: DTerm[?]): DTerm[Among.Traces[Any]] =
    taken(t, "the traces", None) { case Ty.TupleOf(List(Ty.ListOf(_), Ty.ListOf(_))) => }
  def madeSchedule(t: DTerm[?]): DTerm[Map[BigInt, Any]] =
    taken(t, "the schedule", None) { case Ty.MapOf(Ty.Num(NumKind.Big), _) => }

  /** A record's field or a pair's side, by name: the term's own type says whether it has one (`Term.field`). */
  def fieldOf(t: DTerm[?], name: String): DTerm[Any] = t.selectDynamic(name) match
    case field: DTerm[?] => any(field)
    case other           => throw IllegalStateException(s"FrFlow bug: $name of a term is $other")
