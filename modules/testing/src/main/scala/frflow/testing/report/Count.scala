package frflow.testing.report

/** How many cases a run was asked for, and how many it drew and tried: a case that could not be drawn (no value of
  * a type meeting what always holds of it) is not tried, and the shortfall is said.
  */
final case class Count(asked: Int, tried: Int):
  def shortfall: Int = asked - tried
