package crm

import frflow.project.Projects
import frflow.project.pipeline.Analysis
import frflow.proof.lean.print.Print

/** What crm's Lean says of the tables' one row per key (owner §40, 2.6): a store's starting state meets the rule at
  * each store it holds, as the rule's guard places it (the database's tables hold one, a field of its state); a
  * store whose state is a list meets it at each element, and an `always(stored)` at the state itself; and a
  * maker is asked the rule given what the makers its code calls make (their `made_`).
  */
class LeanShapeSuite extends munit.FunSuite:
  private def start(on: Analysis, kb: String, node: String): String =
    on.modules.find(_.name.dotted == s"FrFlowGen.$kb.Whole.Spec").map(Print.module).getOrElse(fail("no statements"))
      .linesIterator.dropWhile(!_.contains(s"def start_$node ")).slice(1, 2).mkString.trim

  test("the tables' starting state meets one row per key at the store they hold") {
    assertEquals(start(Projects.bare(Projects.elaborated(knowledge)), "Crm", "oneRowPerKey"),
      "∀ (s : Tables), (Crm.tablesStartEmpty s) → (Crm.oneRowPerKey s.store)")
  }

  test("a store of a list meets an always[T] at each element; an always(stored) at the state") {
    val rooms = Projects.bare(Projects.rooms)
    assertEquals(start(rooms, "Rooms", "neverOverlap"),
      "∀ (s : (List Booking)), (Rooms.startsEmpty s) → (Rooms.neverOverlap s)")
    val each = start(rooms, "Rooms", "bookingsEndAfterStart")
    assert(each.startsWith("∀ (s : (List Booking)), (Rooms.startsEmpty s) → (∀ "), each)
  }

  test("what the write side makes is asked given what the write it calls makes: its made_, a hypothesis (owner §37)") {
    val spec = Projects.bare(Projects.elaborated(knowledge)).modules
      .find(_.name.dotted == "FrFlowGen.Crm.oneRowPerKey.Spec").map(Print.module).getOrElse(fail("no spec"))
    val saved = spec.linesIterator.dropWhile(!_.contains("def made_save ")).slice(1, 2).mkString
    assert(saved.contains("(m_write : (Crm.oneRowPerKey.makes_write write))") &&
      saved.contains("(Crm.oneRowPerKey.makes_save (Crm.saved storeRows write))"), saved)
  }
