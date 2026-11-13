package frflow.proof.audit

import frflow.core.analysis.resolution.Resolved
import frflow.proof.prover.ast.ProverModule
import frflow.proof.obligation.Obligation

/** What FrFlow checks of the modules it lays out, before any of it is written or checked: every term built into an
  * obligation well-formed (`WellFormed`), and every discharge a rule taken needs, and every obligation a node's place
  * asks, stated (`Completeness`). Either failing is a FrFlow bug: the modules are refused, never laid out short.
  */
object Audit:
  def checked(r: Resolved, obligations: List[Obligation], modules: List[ProverModule]): List[ProverModule] =
    val ill = WellFormed.of(r, obligations).map((o, e) => s"$o: $e")
    val missing = Completeness.of(r, modules).map(m => s"${m.node.value} needs ${m.obligation} (${m.why})")
    if ill.isEmpty && missing.isEmpty then modules
    else throw IllegalStateException(s"FrFlow bug: ${r.theory.name.value}'s modules are not what its theory asks: " +
      (ill.take(5) ++ missing.take(5)).mkString("; "))
