package frflow
package check

import frflow.fixtures.*
import frflow.protocol.*

/** What a check runs, and in what order, from the analysis alone. */
class CheckPlanSuite extends munit.FunSuite:

  private val a = Desk(shelfKb).analysis
  private def ids(ns: List[Node[?]]) = ns.map(_.id)
  private def proven(n: Node[?]) = NodeId(n.id) -> NodeCheck(a.checkHash(n), CheckStatus.Proven, Nil, Nil, Nil, java.time.Instant.EPOCH)

  test("a node is checked after its parts, the nodes of one level side by side") {
    val plan = CheckPlan(a, None)
    assertEquals(ids(plan.todo), List("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    assertEquals(plan.levels.map(ids), List(List("Pick"), List("FromList", "OnlyLong", "EveryLong"), List("OnlyGood")))
    // the models first, in one build
    assertEquals(plan.prebuild, ids(plan.todo).map(id => s"FrFlowGen.Shelf.$id.Spec"))
    assertEquals(plan.theorems(List(pick)), List("FrFlowGen.Shelf.Pick.Theorems"))
  }

  test("a node whose check is current keeps it while its parts are proven; one node is checked whatever its record") {
    val recorded = a.withChecks(Map(proven(pick), proven(fromList)))
    val plan = CheckPlan(recorded, None)
    assertEquals(ids(plan.pending), List("OnlyGood", "OnlyLong", "EveryLong"))
    assertEquals(plan.theorems(List(fromList, onlyLong)), List("FrFlowGen.Shelf.OnlyLong.Theorems"))
    assertEquals(plan.kept(pick, plan.parts(pick, Map.empty)).map(_.status), Some(CheckStatus.Proven))
    // FromList is kept only once Pick, its part, is proven in this run or the record
    assertEquals(plan.parts(fromList, Map.empty), List("Pick" -> Some(CheckStatus.Proven)))
    val failed = Map("Pick" -> NodeCheck(Hash("h"), CheckStatus.Failed, Nil, Nil, Nil, java.time.Instant.EPOCH))
    assertEquals(plan.kept(fromList, plan.parts(fromList, failed)), None)
    // a recorded check of another hash is not current
    val stale = a.withChecks(Map(NodeId("Pick") -> NodeCheck(Hash("old"), CheckStatus.Proven, Nil, Nil, Nil, java.time.Instant.EPOCH)))
    assertEquals(CheckPlan(stale, None).pending.map(_.id).contains("Pick"), true)
    // checking one node: that node, checked again
    val one = CheckPlan(recorded, Some("Pick"))
    assertEquals((ids(one.todo), ids(one.pending)), (List("Pick"), List("Pick")))
  }

  test("check hashes depend on the Lean, not the words: a reworded statement keeps them") {
    def team(statement: String) =
      val top = Node.claim("Top", statement, why = "w")(forall((x: BigInt) => sq(x) >= 0))
      Desk(KnowledgeBase("Team", idea = "IDEA.md")(top, Node.claim("Floor", "Results are at least zero.", why = "w")(forall((x: BigInt) => sq(x) >= 0)).under(top))).analysis
    val (before, after) = (team("Results are never negative."), team("Results are never below zero."))
    def both(f: Analysis => Node[?] => Any, id: String) = (f(before)(before.kb.node(id).getOrElse(fail(id))), f(after)(after.kb.node(id).getOrElse(fail(id))))
    val (h1, h2) = both(_.checkHash, "Top")
    assertEquals(h1, h2)
    val (c1, c2) = both(_.hash, "Top")
    assertNotEquals(c1, c2)
    // the root's depends on everything root_impl composes
    assertNotEquals(a.checkHash(onlyGood), Desk(shelfKb.implementProven(pick)(longOnes)).analysis.checkHash(onlyGood))
  }
