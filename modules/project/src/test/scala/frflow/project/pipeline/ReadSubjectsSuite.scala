package frflow.project.pipeline

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.name.NodeId
import frflow.project.Projects

/** The subjects, in the order decisions are taken: every node after all it rests on, whatever order the model lists
  * them in; a premise's parents are the wholes it is a part of only, never the nodes assuming it.
  */
class ReadSubjectsSuite extends munit.FunSuite:
  private def ids(xs: String*) = xs.map(NodeId(_)).toList
  private val shelf = Kb.of(plain("B"), plain("A"), plain("R"), assumption("P")(Lang.truth))
    .linking(partOf("A", "R"), partOf("B", "A"), assumes("B", "P"))
  private val a = Projects.bare(shelf.elaborated)

  test("the order puts every node after all it rests on, whatever order the model lists them in") {
    assertEquals(a.subjects.inOrder.map(_.id), ids("R", "A", "P", "B"))
  }

  test("a premise is no part: the node assuming it rests on it, and is none of its parents") {
    val (b, p) = (a.subjects.get(NodeId("B")), a.subjects.get(NodeId("P")))
    assertEquals(b.map(s => (s.place.parents, s.place.restsOn)), Some((ids("A"), ids("A", "P"))))
    assertEquals(p.map(s => (s.place.parents, s.place.restsOn)), Some((Nil, Nil)))
  }

  test("links: each claim before the parts below it") {
    val order = Projects.bare(Projects.links).subjects.inOrder.map(_.id.value)
    def before(x: String, y: String) = assert(order.indexOf(x) < order.indexOf(y), order)
    before("removeChangesOnlyThatCode", "removedCodeLeadsNowhere")
    before("removeChangesOnlyThatCode", "removeKeepsOtherCodes")
  }

  test("a node proven of code rests on what its code calls, but on none of its own parts: those come after it") {
    val subjects = Projects.bare(Projects.links).subjects
    val remove = subjects.get(NodeId("removeChangesOnlyThatCode")).map(_.place.restsOn)
      .getOrElse(fail("no removeChangesOnlyThatCode"))
    assert(!remove.contains(NodeId("removedCodeLeadsNowhere")), remove)
    assert(Projects.bare(Projects.links).decided.reliesOn(NodeId("removeChangesOnlyThatCode")).isEmpty)
  }
