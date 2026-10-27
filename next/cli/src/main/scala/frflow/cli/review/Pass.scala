package frflow.cli.review

import frflow.core.name.NodeId

/** Where a review stands: the nodes skipped (refused ones among them), whether the mechanical batch was offered, and
  * how many decisions it recorded.
  */
final case class Pass(skipped: Set[NodeId], batchOffered: Boolean, decided: Int):
  def skip(id: NodeId): Pass = copy(skipped = skipped + id)
  def recorded(n: Int): Pass = copy(decided = decided + n)

object Pass:
  val start: Pass = Pass(Set.empty, batchOffered = false, decided = 0)
