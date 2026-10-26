package frflow.dsl.node

import frflow.core.name.{NodeId, Span}
import frflow.core.spec.Prose

/** What every node has as written, whatever its kind; its statement is built later (`Node.statement`). */
final case class Head(id: NodeId, prose: Prose, at: Span, links: Links)
