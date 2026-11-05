package frflow.api.node

import frflow.core.expr.Mentions
import frflow.core.spec.NodeKind

/** What a node says: its kind and sentence, its formula as written, how it is checked (in words, read off the
  * formula: `Checking`), what it mentions, and why it holds: the reason of the decision it is bound to (the ledger's,
  * signed), none before one.
  */
final case class Says(kind: NodeKind, statement: String, written: Option[String], checking: List[String],
    mentions: Mentions, reason: Option[String])
