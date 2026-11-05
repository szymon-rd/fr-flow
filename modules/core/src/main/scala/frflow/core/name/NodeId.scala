package frflow.core.name

/** A node's id, as the developer names it (`AccessExactly`): unique in a FrModel. */
opaque type NodeId = String

object NodeId extends Label[NodeId]
