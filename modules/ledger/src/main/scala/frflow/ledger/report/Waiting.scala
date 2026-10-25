package frflow
package ledger
package report

import frflow.protocol.*

object Waiting:
  /** A node with a parent rejected waits to be moved under the node chosen instead. */
  def rejectedParents(a: Annotated, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => a.byId.get(p).exists(_.state == ReviewState.Rejected))

  /** The nodes waiting for a developer's decision, in the order to take them. */
  def forDeveloper(a: Annotated): List[Reviewed] =
    val rank = a.order.zipWithIndex.toMap
    a.nodes.filter(r => (r.state == ReviewState.Proposed || r.state == ReviewState.Review) && rejectedParents(a, r).isEmpty)
      .sortBy(r => rank.getOrElse(r.id, Int.MaxValue))
