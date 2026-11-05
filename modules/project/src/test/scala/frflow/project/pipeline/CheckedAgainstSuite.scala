package frflow.project.pipeline

import frflow.core.analysis.resolution.{Constrained, SaysWhat}
import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.proof.obligation.ObligationName

/** What code a statement is checked against: none of a claim saying what a Declaration is, whose tested Scala only
  * stands in it (2.7), and no `impl` of an assumption, trusted with the proven code standing in it.
  */
class CheckedAgainstSuite extends munit.FunSuite:
  test("a claim saying what a Declaration is is not tested, though it mentions tested Scala: auth's") {
    val t = Projects.elaborated(auth.knowledge).theory
    val saying = t.nodes.map(_.node.id).filter(id => SaysWhat.is(t, id) &&
      Constrained.of(t, id).flatMap(t.code.attached.get).exists(_.code.scala.nonEmpty))
    assert(saying.nonEmpty)
    assertEquals(saying.filter(Testable.of(t, _)), Nil)
  }

  test("an assumption is asked no impl, the code standing in it trusted with it: crm's keyedTables, a rule of the " +
    "stores asked of what the code makes and of the programs keeping it (made_, cover_)") {
    val a = Projects.bare(Projects.elaborated(crm.knowledge))
    val t = a.decided.theory
    assertEquals(SaysWhat.checkedAgainst(t, NodeId("keyedTables")), None)
    val asked = a.obligations.filter(_.node == NodeId("keyedTables")).flatMap(_.required).map(_.name)
    assert(!asked.contains(ObligationName.Impl) && asked.exists(n =>
      frflow.proof.lean.lower.LowerObligation.name(n).text.startsWith("cover_")),
      asked)
  }
