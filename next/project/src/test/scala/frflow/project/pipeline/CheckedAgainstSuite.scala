package frflow.project.pipeline

import frflow.core.analysis.{Callees, Constrained, SaysWhat}
import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.proof.obligation.ObligationName

/** What code a statement is checked against: none of a claim saying what a Declaration is, whose tested Scala only
  * stands in it (2.7), and no `impl` of an assumption, trusted with the proven code standing in it.
  */
class CheckedAgainstSuite extends munit.FunSuite:
  test("a claim saying what a Declaration is is not tested, though it mentions tested Scala: keycloak's") {
    val t = Projects.elaborated(keycloak.knowledge).theory
    val saying = t.nodes.map(_.node.id).filter(id => SaysWhat.is(t, id) &&
      Constrained.of(t, id).flatMap(t.code.attached.get).exists(_.code.scala.nonEmpty))
    assert(saying.nonEmpty)
    assertEquals(saying.filter(Testable.of(t, _)), Nil)
  }

  test("an assumption mentioning proven code is asked no impl: crm's crmRun") {
    val a = Projects.bare(Projects.elaborated(crm.knowledge))
    val t = a.decided.theory
    assert(Callees.of(t, NodeId("crmRun")).nonEmpty)
    assertEquals(SaysWhat.checkedAgainst(t, NodeId("crmRun")), None)
    assert(!a.obligations.filter(_.node == NodeId("crmRun")).flatMap(_.required).exists(_.name == ObligationName.Impl))
  }
