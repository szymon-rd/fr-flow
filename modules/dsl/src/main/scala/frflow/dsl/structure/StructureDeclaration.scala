package frflow.dsl.structure

import frflow.core.name.SymbolName
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.build.WrittenAt
import frflow.dsl.term.{LeanType, Lift, Term}
import frflow.dsl.vocab.{Declaration, Definition, Stating}
import scala.annotation.publicInBinary

/** A member of a structure as its Definition has it: its name, whether it changes the structure (Scala's `update`),
  * and its inputs' and its result's types.
  */
final case class Member(name: String, changes: Boolean, params: List[LeanType[?]], result: LeanType[?])

object StructureDeclaration:
  /** What a structure of the type `holder` holds as the word `part`: a word of its own
    * (`paymentHandler_holds_ledger`), a function from the holder to what it holds. It has its code where the
    * holder's class is given the words of what it holds (`lifted[StreamHandler](limits, ledger, offsets)`).
    */
  def held(holder: LeanType[?], part: SymbolName, is: LeanType[?]): Definition[Any] =
    val of = holder.ty match
      case Ty.Data(name) => name.value
      case other         => other.toString
    new Definition[Any](SymbolName(s"${of.take(1).toLowerCase}${of.drop(1)}_holds_${part.value}"),
      s"the ${part.value} a $of holds", None, WrittenAt.none)(
      using LeanType.of[Any](Ty.FnOf(List(holder.ty), is.ty), holder, is))

/** A structure's word: a Declaration of a trait's type (`val limits = Declaration[Limits]("…")`). Its members are
  * called in statements as the trait declares them (`limits.authorise(p)`, a `Call`): each is a word of its own
  * (`limits_authorise`), a function of the structure that gives the member's result, and, of a member that changes
  * the structure, the structure after it. A Definition of it (`limits.define(lifted[SpendLimits])`) gives each
  * member its code, checked against every claim.
  */
final class StructureDeclaration[T] @publicInBinary private[dsl] (val name: SymbolName, val described: String,
    at: WrittenAt, val members: List[Member])(using t: LeanType[T]) extends Declaration[T], Selectable:
  def leanType: LeanType[T] = t
  val word: Definition[T] = new Definition[T](name, described, None, at)
  /** What the structure's states are typed by in a statement: `structure.State` of its name, as `Definition[T]`
    * says.
    */
  type Is
  /** The structure whole, as a statement names it (`(before: limits.State) => …`): one of its states. */
  type State = Term[Is]
  /** How other calls leave the structure before each step of a call, by the step's number (`Call.among`). */
  type Schedule = Term[Map[BigInt, Is]]

  /** The schedule in which no other call does anything (`limits.nobody.updated(BigInt(2), left)`: the others
    * leave the structure as `left` before the call's second step).
    */
  def nobody: Schedule = Lift.constant(Map.empty[BigInt, Is])(using
    LeanType[Map[BigInt, T]].asInstanceOf[LeanType[Map[BigInt, Is]]]) // a state is typed by the structure's name

  /** The Definition a member is: named after the structure's and the member's. */
  def member(called: String): Definition[Any] =
    val m = members.find(_.name == called).getOrElse(throw IllegalStateException(s"FrFlow bug: no member $called"))
    val result = if m.changes then Ty.TupleOf(List(m.result.ty, t.ty)) else m.result.ty
    new Definition[Any](SymbolName(s"${name.value}_$called"), s"$called of ${name.value}", None, at)(
      using LeanType.of[Any](Ty.FnOf(t.ty :: m.params.map(_.ty), result), (t :: m.result :: m.params)*))

  /** The Definition a member that changes the structure is among other calls (`Call.among`): from the structure,
    * how the others leave it before each step, and the member's inputs, the member's result with the structure
    * after it, and what was done (`Call.Traces`).
    */
  def among(called: String): Definition[Any] =
    val m = members.find(_.name == called).getOrElse(throw IllegalStateException(s"FrFlow bug: no member $called"))
    val steps = Ty.ListOf(Ty.TupleOf(List(t.ty, t.ty)))
    val gives = Ty.TupleOf(List(Ty.TupleOf(List(m.result.ty, t.ty)), Ty.TupleOf(List(steps, steps))))
    new Definition[Any](SymbolName(s"${name.value}_${called}_among"), s"$called of ${name.value}, among other " +
      "calls", None, at)(using LeanType.of[Any](Ty.FnOf(t.ty :: Ty.MapOf(Ty.Num(NumKind.Big), t.ty) ::
      m.params.map(_.ty), gives), (t :: m.result :: m.params)*))

  /** A member called on the structure as it stands (`limits.authorise(p)`), as Scala's structural types call one. */
  def applyDynamic(called: String)(args: Any*)(using st: Stating): Any =
    Call.of(this, called, st.standing(this), args.toList)
  def selectDynamic(called: String)(using st: Stating): Any = Call.of(this, called, st.standing(this), Nil)

  /** The structure as it stands, where a statement speaks of it whole (`checkpoint.commit(o).after ===
    * checkpoint.current`).
    */
  def current(using st: Stating): State = st.standing(this).asInstanceOf[State] // a state is typed by the name
