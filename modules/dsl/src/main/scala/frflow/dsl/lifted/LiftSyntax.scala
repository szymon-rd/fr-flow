package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.core.ty.Ty
import frflow.dsl.build.{Fault, Source, WrittenAt}
import frflow.dsl.lifted.steps.ServiceLift
import frflow.dsl.node.AlwaysSyntax
import frflow.dsl.service.ServiceImplementation
import frflow.dsl.term.{Notes, Term, Terms, TermSyntax}

/** `lifted { (a: A, b: B) => … }`: plain Scala as a Definition given its meaning where it is written. The compiler
  * reads the function's body into a term (`Reader`: a compile error on Scala outside what it reads), and the
  * function stays the Scala it is (`Lifted.native`). Every type of a value in it has an `FrSpec`. To four inputs.
  */
object LiftSyntax:
  inline def lifted[A: FrSpec, R: FrSpec](inline f: A => R): Lifted.Of1[A, R] =
    Lifted.Of1(Lifting.one[A, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read1[A, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, R: FrSpec](inline f: (A, B) => R): Lifted.Of2[A, B, R] =
    Lifted.Of2(Lifting.two[A, B, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read2[A, B, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, C: FrSpec, R: FrSpec](inline f: (A, B, C) => R): Lifted.Of3[A, B, C, R] =
    Lifted.Of3(Lifting.three[A, B, C, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read3[A, B, C, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, C: FrSpec, D: FrSpec, R: FrSpec](inline f: (A, B, C, D) => R)
      : Lifted.Of4[A, B, C, D, R] =
    Lifted.Of4(Lifting.four[A, B, C, D, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read4[A, B, C, D, R](f)), f)

  /** `lifted { granted(RoomBookings("Oak", Nil), Booking("Oak", 9, 10)) }`: a closed fact in plain Scala as its
    * term, what an example states (`FrFlowExamples`): lifted functions called on values written out.
    */
  inline def lifted(inline fact: Boolean): Term[Boolean] = LiftMacro.fact(fact)

  /** `lifted(SpendLimits(BigInt(100), Nil))`: a class that implements a service, read member by member: what a
    * service's Definition is given (`implementProven(limits)(lifted(…))`), each member checked against every
    * claim on it (`steps.ServiceLift`).
    */
  inline def lifted[T](inline service: T): ServiceImplementation[T] = ${ ServiceLift.read[T]('service) }

  /** `always` of a type's contract, a node's whole formula (`Node.assumption("…")(contractOf[Booking])`: an
    * assumption of a type from outside, a claim of one the code makes): the rule a define named as the node's val,
    * as `always[T](x => …)` makes one. Of a type whose spec states no contract, a fault on the node.
    */
  inline def contractOf[A](using s: FrSpec[A]): Term[Boolean] =
    stating(s, DefName(Source.valName), WrittenAt.in(Source.here))

  def stating[A](s: FrSpec[A], name: DefName, at: WrittenAt): Term[Boolean] = s.contract.fold(
    Term.noted(Notes.fault(Fault.NoContract(Ty.names(s.ty).headOption.fold(s.ty.toString)(_.value))))(
      TermSyntax.True.run))(c => Terms.always[A](c.written.params.headOption.getOrElse("x"),
        AlwaysSyntax.applied(Lifting.stated[A](name, at, c.written)(c.rule)(using s)))(using s))
