package frflow
package flow

/** A run on the models that failed with `error`: what an example of a flow gives as its result for a run that fails
  * (`expect(request, before.failing(true), Failed(Failure.StoreUnavailable), before, "the store is down")`).
  */
final case class Failed(error: Any):
  override def toString: String = s"Failed(${Example.show(error)})"
