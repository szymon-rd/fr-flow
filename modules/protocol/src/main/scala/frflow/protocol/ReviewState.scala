package frflow.protocol

/** Where the developer stands on a node: `proposed` (not decided yet, or rejected then reworked),
  * `accepted`, `review` (something moved since: see `Cause`), or `rejected` (an alternative was chosen).
  */
enum ReviewState:
  case Proposed, Accepted, Review, Rejected
  override def toString: String = word(productPrefix)

object ReviewState extends Words[ReviewState]
