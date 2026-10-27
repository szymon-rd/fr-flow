package frflow.proof.verdict

/** A check that ends at a judge: the status, the results so far, and why. */
final case class Judged(status: CheckStatus, results: List[Result], findings: List[Finding])
