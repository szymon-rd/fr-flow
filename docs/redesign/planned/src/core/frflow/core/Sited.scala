package frflow.core

import frflow.core.name.Span
import frflow.core.spec.Node

/** A node and where it is written: every node has a position, by construction. */
final case class Sited(node: Node, at: Span)
