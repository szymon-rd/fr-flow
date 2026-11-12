package frflow.project.pipeline

import frflow.core.analysis.resolution.{Constrained, SaysWhat}
import frflow.project.Projects

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
