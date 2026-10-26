package frflow.runtime

import frflow.core.name.NodeId
import frflow.eval.{Env, ScalaValue}
import frflow.eval.run.{Broken, CallCheck}
import frflow.runtime.check.{AssumptionWatch, CallValues}

/** What a service checks of each call: its result against the contract, on the calls sampled; the assumptions about
  * the values it ran with, on every call (cheap: once per change).
  */
final case class Guard(contract: NodeId, check: CallCheck, sampled: () => Boolean, watch: AssumptionWatch):
  def result(call: List[ScalaValue]): Option[Broken] = if sampled() then check.broken(call, Env.inForce) else None
  def values(now: CallValues): Option[Broken] = watch.broken(now).map(Broken.Assumption(_))
