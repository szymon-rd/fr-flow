package frflow.dsl.service

import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.dsl.build.WrittenAt
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, Stating}
import scala.annotation.publicInBinary

/** A member of a service as its Definition has it: its name, whether it changes the service (Scala's `update`),
  * and its inputs' and its result's types.
  */
final case class Member(name: String, changes: Boolean, params: List[LeanType[?]], result: LeanType[?])

/** A Definition of a service: a value of a trait's type (`val limits = Definition[Limits]("…")`). As a term it is
  * the service as it stands. Its members are called in statements as the trait declares them
  * (`limits.authorise(p)`, a `Call`): each is a Definition of its own (`limits_authorise`), a function of the
  * service that gives the member's result, and, of a member that changes the service, the service after it. The
  * value provided for the Definition (`implementProven`) gives each member its code, checked against every claim.
  */
final class ServiceDefinition[T] @publicInBinary private[dsl] (name: SymbolName, described: String, at: WrittenAt,
    val members: List[Member])(using t: LeanType[T]) extends Definition[T](name, described, None, at):
  /** The Definition a member is: named after the service's and the member's. */
  def member(called: String): Definition[Any] =
    val m = members.find(_.name == called).getOrElse(throw IllegalStateException(s"FrFlow bug: no member $called"))
    val result = if m.changes then Ty.TupleOf(List(m.result.ty, t.ty)) else m.result.ty
    new Definition[Any](SymbolName(s"${name.value}_$called"), s"$called of ${name.value}", None, at)(
      using LeanType.of[Any](Ty.FnOf(t.ty :: m.params.map(_.ty), result), (t :: m.result :: m.params)*))

  /** A member called on the service as it stands (`limits.authorise(p)`), as Scala's structural types call one. */
  def applyDynamic(called: String)(args: Any*)(using st: Stating): Any =
    Call.of(this, called, st.standing(this), args.toList)
  def selectDynamic(called: String)(using st: Stating): Any = Call.of(this, called, st.standing(this), Nil)

  /** The service as it stands, where a statement speaks of it whole (`checkpoint.commit(o).after ===
    * checkpoint.current`).
    */
  def current(using st: Stating): Term[T] = st.standing(this)

object ServiceDefinition:
  /** Where code FrFlow reads names a service by its Definition (`lifted(StreamProcessor(limits, …))`), the
    * Definition stands for the service. Nothing runs it: FrFlow reads the code, it does not call it.
    */
  given standsFor[T]: Conversion[ServiceDefinition[T], T] = d =>
    throw IllegalStateException(s"FrFlow: ${d.name.value} is a service's Definition: it stands for the service " +
      "only in code FrFlow reads (`lifted(…)`), and is not the service itself")
