package frflow.dsl.node

import frflow.core.spec.{Reliance, Statement}
import frflow.dsl.build.Fault
import frflow.dsl.node.NodeSyntax.*
import frflow.dsl.term.TermSyntax.True

/** The fluent methods of the three kinds of nodes: `.leftOpenAbove` is a claim's, the edges every node's. */
class NodeSyntaxSuite extends munit.FunSuite:
  private val open = Node.claim("Holds.")(True).leftOpenAbove
  private val trusted = Node.assumption("Holds.")(True).leftOpenAbove

  test("a claim left open above is one the nodes above do not rely on for the word it fixes") {
    assertEquals(open.statement.run.toOption.map(_._2.relied), Some(Reliance.LeftOpen))
    assert(open.statement.run.toOption.exists(_._2 match { case Statement.Claim(_, _) => true; case _ => false }))
  }

  test("an assumption has no nodes relying on it above, so `.leftOpenAbove` on one is a fault on the node") {
    assertEquals(trusted.statement.run.fold(_.toNonEmptyList.toList.map(_.fault), _ => Nil),
      List(Fault.NotAClaim("leftOpenAbove")))
  }
