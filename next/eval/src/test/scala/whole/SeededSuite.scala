package whole

import frflow.core.consistency.{Consistency, Group, Witness}
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.proof.layout.Lowering
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{ObligationName, Prop, Required, Substitute}
import frflow.proof.terms.TermTable
import frflow.proof.whole.Stands

/** The step 12 review's seeded models, read before Lean: proven code reached only through other proven code stands
  * in a consistency statement (B1), so does a provided value it reaches, universal (RR1), and statements pinning one
  * provided value are in one group (S1).
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

  test("a provided value reached only through the code standing in a group is universal, with what the world says") {
    val groups = Consistency.of(Theories.theory(Seeded.Through.knowledge)).collect { case g: Group.Sharing => g }
    assertEquals(groups.map(g => (g.statements.map(_.value), g.open, g.provided, g.premises.map(_.value))),
      List((List("holdsB", "holdsA"), List(s("holds")), List(s("k")), List("kPositive"))))
  }

  test("an existential never binds a Definition with a meaning of its own left in its body; a universal may") {
    def printed(kb: frflow.FrModel, p: Prop): String =
      val r = Theories.resolved(kb)
      Print.expr(Lowering(r, TermTable.of(r)).props.statement(p))
    val hidden = Prop.ClaimOf(NodeId("holdsIs"), Map.empty)
    val some = printed(Seeded.Hidden.knowledge, Prop.ForSome(List(s("holds")), hidden))
    assert(some.startsWith("∃ (holds : ") && !some.contains("(outer : "), some)
    assert(printed(Seeded.Hidden.knowledge, Prop.ForEvery(List(s("holds")), hidden)).contains("(outer : "))
    val through = Prop.ClaimOf(NodeId("holdsA"), Map(s("outer") -> Substitute.Code(DefName("through")),
      s("inner") -> Substitute.Code(DefName("maybe"))))
    val provided = printed(Seeded.Through.knowledge, Prop.ForSome(List(s("holds")), through))
    assert(provided.contains("(Through.maybe k)") && !provided.contains("(k : "), provided)
  }

  test("the premises over one provided value are asked to hold together, witnessed where a bound or nothing meets") {
    val vacuous = Consistency.of(Theories.theory(Seeded.Vacuous.knowledge)).collect { case g: Group.Premises => g }
    assertEquals(vacuous.map(g => (g.statements.map(_.value), g.provided)),
      List((List("kPositive", "kNegative"), List(s("k")))))
    val fresh = Consistency.of(Theories.theory(keycloak.knowledge)).collect { case g: Group.Premises => g }
    assertEquals(fresh.map(g => (g.statements.map(_.value), g.provided, g.witnesses)),
      List((List("freshTokens"), List(s("history")), List(Witness.Empty(s("history"))))))
  }

  test("an assumption every word of which the code gives a meaning is asked impl: nothing else checks it") {
    val r = Theories.resolved(Seeded.Trusted.knowledge)
    assert(Required.of(r, Set.empty, NodeId("outerKeeps")).exists(_.name == ObligationName.Impl))
    assertEquals(Consistency.of(r.theory).collect { case g: Group.Sharing => g.statements.map(_.value) },
      List(List("holdsIs")))
  }

  test("an assumption with no word at all is asked to be proven, nothing standing in it") {
    val r = Theories.resolved(Seeded.Pure(3).knowledge)
    assertEquals(Required.of(r, Set.empty, NodeId("noDouble")).map(_.name), List(ObligationName.Impl))
  }
