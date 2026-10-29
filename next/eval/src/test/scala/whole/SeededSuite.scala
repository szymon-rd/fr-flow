package whole

import frflow.core.consistency.{Consistency, Group}
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.proof.obligation.Substitute
import frflow.proof.whole.Stands

/** The step 12 review's seeded models, read before Lean: proven code reached only through other proven code stands
  * in a consistency statement (B1), and statements pinning one provided value are in one group (S1).
  */
class SeededSuite extends munit.FunSuite:
  private def s(v: String) = SymbolName(v)

  test("the code standing in a statement stands for what it calls too: inner's, reached only through outer's") {
    val r = Theories.resolved(Seeded.Hidden.knowledge)
    assertEquals(Stands.of(r, List(s("outer"))),
      Map(s("outer") -> Substitute.Code(DefName("through")), s("inner") -> Substitute.Code(DefName("twice"))))
    assertEquals(Consistency.open(r.theory, NodeId("holdsIs")), List(s("holds")))
  }

  test("assumptions pinning one provided value apart are one group, solving it once") {
    val groups = Consistency.of(Theories.theory(Seeded.TwoPins.knowledge)).collect { case g: Group.Sharing => g }
    assertEquals(groups.map(_.statements.map(_.value).toSet),
      List(Set("nIsD1", "d1IsZero", "nIsD2", "d2IsOne")))
    assertEquals((groups.head.open.toSet, groups.head.provided), (Set(s("d1"), s("d2"), s("n")), Nil))
  }

  test("assumptions whose only value is a pinned provided one have a group") {
    val groups = Consistency.of(Theories.theory(Seeded.Closed.knowledge)).collect { case g: Group.Sharing => g }
    assertEquals(groups.map(g => (g.statements.map(_.value), g.open)), List((List("nIsZero", "nIsOne"), List(s("n")))))
  }
