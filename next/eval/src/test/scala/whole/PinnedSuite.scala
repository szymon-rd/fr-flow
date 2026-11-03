package whole

import frflow.core.consistency.{Consistency, Group, Witness}
import frflow.core.name.{NodeId, SymbolName}

/** A provided value an assumption of its group equates to a term is solved by that equation, like an open value
  * (step 12 ruling, 2.8): crm's store by `crmRun`; a provided value no assumption
  * pins stays universal (auth's session table, which `tokensIssuedOnce` only bounds).
  */
class PinnedSuite extends munit.FunSuite:
  private def group(kb: frflow.FrModel, node: String): Group.Sharing =
    Consistency.of(Theories.theory(kb)).collectFirst {
      case g @ Group.Sharing(ids, _, _, _, _) if ids.contains(NodeId(node)) => g
    }.getOrElse(fail(s"no group of $node"))

  private def pinnedBy(g: Group.Sharing, s: SymbolName): Option[NodeId] = g.witnesses.collectFirst {
    case Witness.Equation(x, from, _) if x == s => from
  }

  test("keycloak: nothing is provided, the server's state the World's (owner §45 D); what is assumed of the store's " +
    "operations known only by assumptions is asked to hold together, each open") {
    val g = group(keycloak.knowledge, "sessionLookup")
    assertEquals(g.provided, Nil)
    assert(List("lookup", "record").map(SymbolName(_)).forall(g.open.contains), g)
  }

  test("crm: what the CRM holds is solved by crmRun, with every statement mentioning it; history and clock universal") {
    val g = group(crm.knowledge, "crmRun")
    assertEquals((g.open, g.provided), (List("finds", "fetch", "storeRows", "held").map(SymbolName(_)),
      List(SymbolName("history"), SymbolName("clock"))))
    assert(g.statements.contains(NodeId("recordsByQuery")), g)
    assertEquals(pinnedBy(g, SymbolName("held")).map(_.value), Some("crmRun"))
  }

  test("a provided value no assumption equates to a term is asked of every value: auth's session table") {
    val g = group(auth.knowledge, "decisionContract")
    assert(g.provided.contains(SymbolName("sessions")) && !g.open.contains(SymbolName("sessions")), g)
  }
