package frflow.dsl.node

import frflow.core.name.NodeId

/** A node another names (`.under(p)`): by id, or `DeclaredLater` when the val was not set yet (Scala initializes vals
  * in order, so it was `null`).
  */
enum Parent:
  case Declared(id: NodeId)
  case DeclaredLater

object Parent:
  def of(n: Node[?, ?] | Null): Parent = n match
    case null           => DeclaredLater
    case n: Node[?, ?]  => Declared(n.head.id)
