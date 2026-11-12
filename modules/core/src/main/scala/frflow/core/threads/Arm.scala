package frflow.core.threads

/** One arm of a `match`: `| pattern => body`. */
final case class Arm(pattern: Pattern, body: Term)
