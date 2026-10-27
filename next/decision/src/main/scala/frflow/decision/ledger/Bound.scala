package frflow.decision.ledger

import frflow.decision.content.{Chain, CodeFingerprint, Content}

/** What a decision is bound to: the node's content as seen (in the form it was projected in), the chain of what it
  * rested on, and the code it governed.
  */
final case class Bound(content: Content, chain: Chain, code: Option[CodeFingerprint])
