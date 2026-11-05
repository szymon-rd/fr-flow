package frflow.cli.command

/** A decision as asked: why (asked for on a terminal when not given), by whom, and whether it is confirmed already
  * (`--yes`: what it records is not shown first).
  */
final case class Asked(reason: Option[String], as: Option[String], yes: Boolean)
