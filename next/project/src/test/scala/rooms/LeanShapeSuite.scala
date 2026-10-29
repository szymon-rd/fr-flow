package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.project.pipeline.Analysis
import frflow.proof.lean.print.Print

/** What rooms' Lean says of where the rules sit (2.4, owner §33): a statement over a world states the rules of the
  * stores it reads of that world, as hypotheses; no node's module imports a rule's module (a rule is a define,
  * not a part); and the theory's own check (`Whole`) is keyed by what each Declaration is.
  */
class LeanShapeSuite extends munit.FunSuite:
  private val a = Projects.bare(Projects.rooms)

  private def module(on: Analysis, name: String): String =
    on.modules.find(_.name.dotted == s"FrFlowGen.Rooms.$name").map(Print.module).getOrElse(fail(s"no module $name"))

  test("bookedIsStored's claim states neverOverlap and bookingsEndAfterStart of now's bookings") {
    val spec = module(a, "bookedIsStored.Spec")
    val claim = spec.linesIterator.dropWhile(!_.contains("def claim")).take(2).mkString("\n")
    assert(claim.contains("(Rooms.neverOverlap now.storedBookings)"), claim)
    assert(claim.contains("(∀ b ∈ now.storedBookings, (Rooms.bookingsEndAfterStart b))"), claim)
  }

  test("no module imports a rule's own: storeWhenFree's spec imports the rules' defines, not their specs") {
    val imports = module(a, "storeWhenFree.Spec").linesIterator.filter(_.startsWith("import ")).toList
    assert(imports.contains("import FrFlowGen.Rooms.Domain.Def_bookingsEndAfterStart"), imports)
    val rules = List("neverOverlap", "bookingsOfTheRoom", "roomBookingsApart", "bookingsEndAfterStart")
    def own(m: String, r: String) = m.startsWith(s"FrFlowGen.Rooms.$r.")
    a.modules.foreach(m => assertEquals(m.imports.map(_.dotted).filter(i =>
      rules.exists(r => own(i, r) && !own(m.name.dotted, r))), Nil, m.name.dotted))
  }

  test("changing what a Declaration is, and nothing else, checks the theory's consistency again") {
    val bookedIsStored = Node.claim("What is booked is what the table holds.")(
      forall((now: Term[World]) => booked(now) === storedBookings.in(now).filter(b => b.start < b.end)))
      .refines(bookWhenFree, acceptWhenFree)
    val kb = FrModel("Rooms")(rooms.nodes.map(n => if n eq _root_.rooms.bookedIsStored then bookedIsStored else n)*)
      .copy(generators = rooms.generators).implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
    val moved = Projects.bare(Projects.elaborated(kb))
    assertNotEquals(moved.keys.whole, a.keys.whole)
    assertEquals(moved.keys.node(NodeId("grantWhenNoOverlap")), a.keys.node(NodeId("grantWhenNoOverlap")))
  }
