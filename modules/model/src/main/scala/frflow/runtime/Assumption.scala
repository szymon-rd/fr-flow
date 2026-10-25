package frflow
package runtime

final case class Assumption(what: String, reads: Set[String], holds: () => Boolean)
