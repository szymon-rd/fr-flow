package frflow.cli
package command

/** A decision as asked: why (asked for on a terminal), by whom, and whether it is confirmed already. */
final case class Asked(reason: Option[String], as: Option[String], yes: Boolean)
