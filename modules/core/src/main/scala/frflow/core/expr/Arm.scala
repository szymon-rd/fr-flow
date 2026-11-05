package frflow.core.expr

/** One case of a match: its pattern and its body. */
final case class Arm(pattern: Pattern, body: Expr)
