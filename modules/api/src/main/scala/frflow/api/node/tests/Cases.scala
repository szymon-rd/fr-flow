package frflow.api.node.tests

/** How many cases a run was asked for and how many it drew and tried (a case not drawn is not tried), and the seed
  * that draws them again.
  */
final case class Cases(asked: Int, tried: Int, seed: Long):
  def shortfall: Int = asked - tried
