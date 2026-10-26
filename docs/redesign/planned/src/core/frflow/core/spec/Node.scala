package frflow.core.spec

import frflow.core.name.NodeId

/** One decided statement: its id, its words, and what it says. Its edges, code, position and checks are kept apart. */
final case class Node(id: NodeId, prose: Prose, statement: Statement)
