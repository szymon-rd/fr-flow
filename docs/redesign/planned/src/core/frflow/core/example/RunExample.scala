package frflow.core.example

import frflow.core.expr.Value

/** A run of a flow under `givens`: its inputs, the world before, and how it ends. */
final case class RunExample(note: String, givens: List[Given], inputs: List[Value], before: Value.World,
    end: RunEnd, verdict: Verdict)
