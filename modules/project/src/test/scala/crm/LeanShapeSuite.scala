package crm

import frflow.core.example.Example
import frflow.core.name.NodeId
import frflow.decision.review.Unproven
import frflow.project.Projects
import frflow.eval.run.OnCode
import frflow.project.pipeline.{Analysis, Computed, ReadProof}
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

  test("each example's obligation is named by its class and its place there, whatever order the classes are read in " +
    "(the PortSuite's, or check's, which finds them by name)") {
    val sets = List(WriteExamples(), ExpireExamples()).map(_.elaborated.fold(es => fail(es.toString), identity))
    def asked(in: List[List[Example]]) =
      val b = Projects.bare(Projects.elaborated(knowledge))
      Analysis(b.valid, b.inputs, Computed(in.flatten.map(_ -> OnCode.Holds), Map.empty)).whole
        .filter(_.name match { case ObligationName.Example(_, _) => true; case _ => false }).toSet
    val (asPorted, asChecked) = (asked(sets), asked(sets.reverse))
    assertEquals(asPorted, asChecked)
    assertEquals(asPorted.map(_.name), ((0 to 5).map(ObligationName.Example("WriteExamples", _)) ++
      (0 to 3).map(ObligationName.Example("ExpireExamples", _))).toSet)
  }

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

  test("a step with parts over the screens' programs rests on what is assumed of the database's search they call " +
    "(G2): its impl takes recordsByQuery and searchKeeps beside its parts") {
    val a = Projects.bare(Projects.elaborated(knowledge))
    val spec = a.modules.find(_.name.dotted == "FrFlowGen.Crm.visibility.Spec").map(Print.module)
      .getOrElse(fail("no spec"))
    val impl = spec.linesIterator.dropWhile(!_.contains("def impl ")).slice(1, 2).mkString
    assert(List("recordsByQuery", "searchKeeps").forall(n => impl.contains(s"(h_$n : (Crm.$n.claim fetch))")), impl)
    assert(a.decided.theory.refinement.parts(NodeId("visibility")).nonEmpty)
  }
