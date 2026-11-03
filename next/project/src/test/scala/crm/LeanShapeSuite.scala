package crm

import frflow.core.name.NodeId
import frflow.decision.review.Unproven
import frflow.project.Projects
import frflow.project.pipeline.{Analysis, ReadProof}
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{ObligationName, TryKind}

/** What crm's Lean says of the tables' one row per key (owner §40, 2.6): a store's starting state meets the rule at
  * each store it holds, as the rule's guard places it (the database's tables hold one, a field of its state); a
  * store whose state is a list meets it at each element, and an `always(stored)` at the state itself; and what a
  * program hands an operation is asked the rule at the call (`made_<program>_call_<i>`).
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

  test("what the write side hands the database is asked of the write's code it calls: made_ at the call (owner §37)") {
    val spec = Projects.bare(Projects.elaborated(knowledge)).modules
      .find(_.name.dotted == "FrFlowGen.Crm.oneRowPerKey.Spec").map(Print.module).getOrElse(fail("no spec"))
    def body(d: String) = spec.linesIterator.dropWhile(!_.contains(s"def $d ")).slice(1, 2).mkString.trim
    assertEquals(body("made_saved_call_1"), "Crm.oneRowPerKey.makes_saved_call_1")
    val made = body("makes_saved_call_1")
    assert(made.endsWith("(Crm.oneRowPerKey (Crm.applyWrite r w)))))"), made)
    assertEquals(body("made_save"), "(Crm.oneRowPerKey.makes_save Crm.saved_run)")
  }

  test("a step over what makers make takes their made_ (step 12 ruling), and rests on it: unproven, the step is red") {
    val a = Projects.bare(Projects.elaborated(knowledge))
    val spec = a.modules.find(_.name.dotted == "FrFlowGen.Crm.storeMirrorsRequests.Spec").map(Print.module)
      .getOrElse(fail("no spec"))
    val complete = spec.linesIterator.dropWhile(!_.contains("def complete ")).slice(1, 2).mkString
    assert(List("keyedTables", "oneRowPerKey").forall(r => complete.contains(s"(m_${r}_expire : (Crm.$r.makes_expire " +
      "expire))")), complete)
    val node = a.decided.theory.node(NodeId("storeMirrorsRequests")).getOrElse(fail("no node"))
    val unproven = ReadProof.of(a, node).unproven
    assert(unproven.contains(Unproven.Kept(NodeId("keyedTables"))) &&
      unproven.contains(Unproven.Kept(NodeId("oneRowPerKey"))), unproven)
  }

  test("the idle try is asked where the Definitions a claim speaks of are functions: the job's expire; the roots, " +
    "over the screens' runs, programs now, are asked none") {
    val tried = Projects.bare(Projects.elaborated(knowledge)).obligations
      .filter(_.tried.exists(_.name == ObligationName.Tried(TryKind.Idle))).map(_.node.value)
    assertEquals(tried, List("expiryJob"))
  }
