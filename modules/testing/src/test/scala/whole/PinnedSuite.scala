package whole

import frflow.core.consistency.{Consistency, Group}
import frflow.core.name.{NodeId, SymbolName}

/** A provided value an assumption of its group equates to a term is solved by that equation, like an open value
  * (step 12 ruling, 2.8; `SeededSuite`'s two pins); a provided value no assumption pins stays universal (auth's
  * session table, which `tokensIssuedOnce` only bounds). Keycloak's and crm's histories and stores are the World's
  * now (owner §45 D): what their groups leave open is what is assumed of the operations known only by assumptions.
  */
class PinnedSuite extends munit.FunSuite:
  private def group(kb: frflow.FrModel, node: String): Group.Sharing =
    Consistency.of(Theories.theory(kb)).collectFirst {
      case g @ Group.Sharing(ids, _, _, _, _) if ids.contains(NodeId(node)) => g
    }.getOrElse(fail(s"no group of $node"))

  test("a provided value no assumption equates to a term is asked of every value: auth's session table") {
    val g = group(auth.knowledge, "decisionContract")
    assert(g.provided.contains(SymbolName("sessions")) && !g.open.contains(SymbolName("sessions")), g)
  }
