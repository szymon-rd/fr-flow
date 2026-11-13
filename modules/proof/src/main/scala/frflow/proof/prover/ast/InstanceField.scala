package frflow.proof.prover.ast

/** One field of an `instance … where`: `logEvent e := …`. */
final case class InstanceField(name: ProverName, params: List[ProverName], value: LExpr)
