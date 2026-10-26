package frflow.api.view

import frflow.core.code.RunCheck
import frflow.decision.review.ReviewState
import frflow.proof.verdict.CheckStatus

/** The counts every view closes with, by concept; derived from the view by `Views.overview`. */
final case class Overview(review: Tally[ReviewState], checks: Tally[CheckStatus], code: Tally[Piece],
    runChecks: Tally[RunCheck], examples: Tally[Boolean], complete: Boolean)
