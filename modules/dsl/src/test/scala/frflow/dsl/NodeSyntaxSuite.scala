package frflow.dsl

import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{Reliance, Statement}
import frflow.dsl.build.Fault
import frflow.dsl.node.*
import frflow.dsl.node.NodeSyntax.*
import frflow.dsl.term.TermSyntax.{True, ||}

/** The fluent methods of the three kinds of nodes: `.leftOpenAbove` is a claim's, the edges every node's. */
class NodeSyntaxSuite extends munit.FunSuite:
  private val open = Node.claim("Holds.")(True).leftOpenAbove
  private val trusted = Node.assumption("Holds.")(True).leftOpenAbove

  test("a claim left open above is one the nodes above do not rely on for the word it fixes") {
    assertEquals(open.alone.run.toOption.map(_._2.relied), Some(Reliance.LeftOpen))
    assert(open.alone.run.toOption.exists(_._2 match { case Statement.Claim(_, _) => true; case _ => false }))
  }

  test("a claim's and an assumption's formula is kept as the model writes it, which the developer decides") {
    def written(n: Node) = n.alone.run.toOption.flatMap(_._2.said).map(_.source.value)
    assertEquals(written(Node.claim("Holds.")(True)), Some("True"))
    assertEquals(written(Node.assumption("Holds.")(True || True)), Some("True || True"))
  }

  private val whole = Node.claim("Holds.")(True).from(part, later)
  private val part = Node.claim("Holds.")(True)
  private val later = Node.assumption("Holds.")(True)

  test("a claim says what it is from where it is stated: the edges its parts' `.refines` gives, of parts declared " +
      "after it too") {
    val written = Edges.of(whole.head).run.toOption.map(_._2)
    assertEquals(written, Some(List(Edge.PartOf(NodeId("part"), NodeId("whole")),
      Edge.PartOf(NodeId("later"), NodeId("whole")))))
    assertEquals(written.map(_.toSet), Some((Edges.of(part.refines(whole).head).run.toOption.toList.flatMap(_._2) ++
      Edges.of(later.refines(whole).head).run.toOption.toList.flatMap(_._2)).toSet))
  }

  test("an assumption has no nodes relying on it above, so `.leftOpenAbove` on one is a fault on the node") {
    assertEquals(trusted.alone.run.fold(_.toNonEmptyList.toList.map(_.fault), _ => Nil),
      List(Fault.NotAClaim("leftOpenAbove")))
  }
