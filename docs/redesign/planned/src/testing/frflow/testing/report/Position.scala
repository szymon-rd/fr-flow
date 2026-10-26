package frflow.testing.report

/** A part of a claim's formula by where it is: the path of child indices from the formula's root
  * (`Exprs.children`), so two equal premises at different places count apart.
  */
final case class Position(path: List[Int])
