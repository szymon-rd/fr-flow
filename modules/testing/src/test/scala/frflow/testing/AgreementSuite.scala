package frflow.testing

import frflow.*
import frflow.eval.Calendar
import frflow.eval.Calendar.{Booking, RoomBookings}
import frflow.testing.Agreement.Outcome
import frflow.testing.report.Seed

/** Lifted code's law, tested: the Scala the JVM runs and the term read from it give one value on generated cases
  * (`Agreement`); and a term that is not the Scala's (another function's, as a reader that misread it would make)
  * is found.
  */
class AgreementSuite extends munit.FunSuite:
  private val settings = Settings(300, Seed(1))
  private val elaborated = Calendar.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the calendar's model is valid") {
    assertEquals(frflow.core.analysis.Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("the calendar's Scala and the terms read from it agree on generated cases") {
    val reports = Agreement.of(elaborated, settings)(Calendar.noOverlap, Calendar.grantedCode)
    assertEquals(reports.map(r => r.code.value -> r.outcome),
      List("noOverlap" -> Outcome.Agree(300), "grantedCode" -> Outcome.Agree(300)))
  }

  test("every case drawn meets its type's contract: a booking ends after it starts") {
    val before = lifted { (b: Booking) => b.start < b.end }
    val notAfter = lifted { (b: Booking) => b.start <= b.end }
    // The term of `before` under the Scala of `notAfter`: they differ only on a booking ending as it starts.
    assertEquals(Agreement(elaborated).between(before, notAfter, settings).outcome, Outcome.Agree(300))
  }

  test("a term that is not the Scala's is found, with the case") {
    val touching = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end < b.start || b.end < a.start }
    Agreement(elaborated).between(Calendar.noOverlap, touching, settings).outcome match
      case Outcome.Differ(inputs, scala, term, _) =>
        assertEquals((scala, term), (Right("false"), Right("true")), inputs.toString)
      case other                                  => fail(s"not found: $other")
  }

  test("lifted code no statement mentions is tested too, its inputs' types read from it") {
    val rooms = lifted { (held: RoomBookings) => held.bookings.map(b => b.room).contains(held.room) }
    assertEquals(Agreement(elaborated).of(rooms, settings).outcome, Outcome.Agree(300))
  }
