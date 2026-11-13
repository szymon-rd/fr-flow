package frflow.dsl

import frflow.core.expr.{Expr, Quantifier}
import frflow.core.ty.Ty
import frflow.dsl.lifted.FrSpec
import frflow.dsl.lifted.LiftSyntax.contractOf
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*

/** The suite's domain: bookings of rooms, as rooms' are. */
object FrSpecSuite:
  final case class Booking(room: String, start: BigInt, end: BigInt) derives FrSpec
  final case class RoomBookings(room: String, bookings: List[Booking]) derives FrSpec

/** A type's contract: written as a statement is, over the value's term, and stated by a node. */
class FrSpecSuite extends munit.FunSuite:
  import FrSpecSuite.*

  test("a type's contract is the rule a node states") {
    val spec = FrSpec.derived[Booking].where(b => b.start < b.end)
    val everyBookingEnds = contractOf[Booking](using spec)
    assertEquals(everyBookingEnds.notes.faults.toList, Nil)
    everyBookingEnds.expr match
      case Expr.Quant(Quantifier.Always, List(x), Expr.Call(rule, _, _)) =>
        assertEquals((x.ty, rule.value), (Ty.Data(frflow.core.name.TypeName("Booking")), "everyBookingEnds"))
      case other                                                        => fail(s"not a rule: $other")
  }

  test("a contract says what a statement can: over every value of a type") {
    val spec = FrSpec.derived[RoomBookings].where(held =>
      forall((t: Term[BigInt]) => held.bookings.forall(b => b.start <= t || t < b.start)))
    val everyTime = contractOf[RoomBookings](using spec)
    everyTime.expr match
      case Expr.Quant(Quantifier.Always, List(x), Expr.Call(rule, _, _)) =>
        assertEquals((x.hint, rule.value), ("held", "everyTime"))
      case other                                                        => fail(s"not a rule: $other")
  }

  test("the last contract given is the type's: a spec has one") {
    val spec = FrSpec.derived[Booking].where(b => b.start < b.end).where(b => b.start <= b.end)
    assertEquals(spec.contract.map(_.written.params), Some(List("b")))
    assertEquals(spec.ty, FrSpec.derived[Booking].ty)
  }

  test("a type whose spec states no contract has none to state: a fault on the node") {
    val nothing = contractOf[RoomBookings]
    assertEquals(nothing.notes.faults.toList.map(_.toString), List("NoContract(RoomBookings)"))
  }
