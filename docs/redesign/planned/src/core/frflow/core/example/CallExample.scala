package frflow.core.example

import frflow.core.expr.Value

/** A call of an operation under `givens`: its inputs and result. */
final case class CallExample(note: String, givens: List[Given], inputs: List[Value], result: Value, verdict: Verdict)
