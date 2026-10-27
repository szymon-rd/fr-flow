package frflow.api.view

import frflow.api.node.lean.CheckState
import frflow.api.view.whole.GroupStatus
import frflow.decision.review.ReviewState

/** The counts every view closes with, by concept (the examples by whether each passes), and whether the project is
  * complete (the CI gate); derived from the view by `Views.overview`.
  */
final case class Overview(review: Tally[ReviewState], checks: Tally[CheckState], code: Tally[Piece],
    consistency: Tally[GroupStatus], examples: Tally[Boolean], complete: Boolean)
