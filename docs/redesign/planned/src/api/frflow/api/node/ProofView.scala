package frflow.api.node

import frflow.eval.run.ExampleResult
import frflow.proof.verdict.{CheckStatus, Finding, Result}

/** What is shown of a node by running things: Lean's check (status, each obligation's result, why it ended), its
  * examples run in Scala, and whether the developer wrote a proof file for it.
  */
final case class ProofView(status: CheckStatus, results: List[Result], findings: List[Finding],
    examples: List[ExampleResult], authored: Boolean)
