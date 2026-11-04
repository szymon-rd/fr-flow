package frflow.api.node

import frflow.core.name.NodeId

/** Where a node sits in the DAG: each related node once per relation, ids only (the front end reads each node from
  * the view). `beside` and `above` are functions of the view (`Views`), not stored.
  */
final case class Placement(root: Boolean, related: List[(Relation, NodeId)]):
  def apply(r: Relation): List[NodeId] = related.collect { case (`r`, n) => n }
