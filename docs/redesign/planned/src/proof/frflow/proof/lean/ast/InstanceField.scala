package frflow.proof.lean.ast

/** One field of an `instance … where`: `logEvent e := …`. */
final case class InstanceField(name: LeanName, params: List[LeanName], value: LExpr)
