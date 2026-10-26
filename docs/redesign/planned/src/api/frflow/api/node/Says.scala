package frflow.api.node

import frflow.core.expr.Mentions
import frflow.core.spec.NodeKind

/** What a node says: its kind, sentence and reason, its formal parts as written, and what they mention. */
final case class Says(kind: NodeKind, statement: String, why: String, written: List[(String, String)],
    mentions: Mentions)
