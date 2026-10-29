package rooms

import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.project.pipeline.Texts

/** How `show` says each of rooms' statements is checked, every line derived (ARCHITECTURE 3.9, which elides some). */
class ShowSuite extends munit.FunSuite:
  private def says(id: String): List[String] = Texts.checking(Projects.rooms.theory, NodeId(id))

  test("booking's claim: proven of its program, resting on the facts its run needs, each with its assumption") {
    assertEquals(says("storeWhenFree"), List(
      "proven of book's program, bookIfGranted",
      "assumed by the code calling book",
      "rules it uses: bookingsEndAfterStart",
      "rests on inRoom and add's Scala, tested against storedBookings",
      "rests on runs on storedBookings being atomic: oneAtATime",
      "rests on what each Booking from outside meets: bookingsEndAfterStart"))
  }

  test("what a Declaration is: the code standing in it, and its group") {
    assertEquals(says("bookedAfterIsStored"), List(
      "says what bookedAfter is: book's program, bookIfGranted, stands in it",
      "consistent with acceptedIsAnswered, grantWhenNoOverlap: witnessed, for Lean to check"))
  }

  test("the calendar's claims: tested, and proven from its parts with the rules it uses apart") {
    assertEquals(says("grantWhenNoOverlap"), List(
      "tested against granted's Scala on generated cases",
      "assumed by the code calling granted",
      "rules it uses: bookingsEndAfterStart",
      "rests on what each Booking from outside meets: bookingsEndAfterStart",
      "consistent with bookedAfterIsStored, acceptedIsAnswered: witnessed, for Lean to check"))
    assertEquals(says("grantWhenFree"), List(
      "proven from its parts (grantWhenNoOverlap)",
      "not checked against granted's Scala: the statement has no Scala value (it quantifies over every value)",
      "assumed by the code calling granted",
      "rules it uses: bookingsOfTheRoom, roomBookingsApart, bookingsEndAfterStart",
      "rests on what each Booking from outside meets: bookingsEndAfterStart"))
  }

  test("the world outside: nothing else writes the table, the programs changing it derived, its runs atomic") {
    assertEquals(says("nothingElseWrites"), List(
      "the world outside: nothing but the code changes storedBookings",
      "the programs changing it, derived: book"))
    assertEquals(says("oneAtATime"), List("the world outside: runs on storedBookings never interleave"))
  }
