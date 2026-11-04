package frflow.decision.review

/** Where the developer stands on a node: not decided yet (or rejected, then reworked), accepted, under review
  * (something moved since: the causes say what), or rejected (an alternative was chosen).
  */
enum ReviewState:
  case Proposed, Accepted, Review, Rejected
