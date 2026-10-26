package frflow.api.node

import frflow.proof.verdict.{CheckStatus, Finding, Result}

/** What is shown of a node by running things: Lean's check (status, each obligation's result, why it ended), and
  * whether the developer wrote a proof file for it. How the node is checked is in `Says.checking`; the examples are
  * the theory's (`WholeView`), not a node's.
  */
final case class ProofView(status: CheckStatus, results: List[Result], findings: List[Finding], authored: Boolean)
