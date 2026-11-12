package frflow.core.term.interpret

/** How many of a formula's leading `forall`s are still to open, and the level the next variable takes. */
final case class Opening(left: Int, level: Int)
