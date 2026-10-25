package frflow
package flow

/** A flow that failed in production with `error` (a value of the flow's error type): the exception `run` fails with
  * when no `handleErrorWith` handles it.
  */
final case class FlowFailed(error: Any) extends RuntimeException(s"the flow failed with ${Example.show(error)}", null, false, false)
