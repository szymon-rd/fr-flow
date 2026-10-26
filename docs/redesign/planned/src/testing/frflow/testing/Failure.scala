package frflow.testing

import frflow.core.expr.Value
import frflow.eval.run.Broken

/** The smallest failing case found: its inputs, what it broke, and where to replay it from. */
final case class Failure(inputs: List[Value], broke: Broken, seed: Seed, index: Int, size: Int)
