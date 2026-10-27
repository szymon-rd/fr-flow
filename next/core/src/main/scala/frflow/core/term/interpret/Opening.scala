package frflow.core.term.interpret

/** How many of a formula's leading `forall`s are still to open, the level the next variable takes, and which side of
  * a run right below them is opened too (of a claim about a program: `Some(false)` its success, `Some(true)` its
  * failure; the outcome and the world after bound outside it).
  */
final case class Opening(left: Int, level: Int, run: Option[Boolean] = None)
