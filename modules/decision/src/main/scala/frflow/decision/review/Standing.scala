package frflow.decision.review

/** A node's review state with the causes that put it there. */
final case class Standing(state: ReviewState, causes: List[Cause])
