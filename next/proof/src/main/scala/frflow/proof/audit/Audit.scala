package frflow.proof.audit

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.Obligation

/** What FrFlow checks of the Lean it lays out, before any of it is written or checked: every term built into an
  * obligation well-formed (`WellFormed`), and every discharge a rule taken needs, and every obligation a node's place
  * asks, stated (`Completeness`). Either failing is a FrFlow bug: the Lean is refused, never laid out short.
  */
object Audit:
  def checked(r: Resolved, obligations: List[Obligation], modules: List[LeanModule]): List[LeanModule] =
    val ill = WellFormed.of(r, obligations).map((o, e) => s"$o: $e")
    val missing = Completeness.of(r, modules).map(m => s"${m.node.value} needs ${m.obligation} (${m.why})")
    if ill.isEmpty && missing.isEmpty then modules
    else throw IllegalStateException(s"FrFlow bug: the Lean of ${r.theory.name.value} is not what its theory asks: " +
      (ill.take(5) ++ missing.take(5)).mkString("; "))
