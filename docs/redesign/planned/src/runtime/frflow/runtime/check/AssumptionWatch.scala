package frflow.runtime.check

import frflow.core.name.{NodeId, SymbolName}
import frflow.dsl.term.Values
import frflow.eval.Env
import frflow.eval.run.Assumes
import java.util.concurrent.atomic.AtomicReference

/** A service's assumptions, each checked again only when a value it reads is not the one it was last found to hold
  * of (the same object: the values are the developer's, compared by reference, as today). `held` is shared by every
  * call of the service; with the samplers' counters (`Sampling`) it is all the running system's shared mutable state.
  */
final class AssumptionWatch(watched: List[Assumes]):
  private val held = AtomicReference(Map.empty[NodeId, List[Any]])

  /** The first assumption the call's values break, of those whose values the call loaded. */
  def broken(call: CallValues): Option[NodeId] =
    watched.filter(_.reads.forall(call.loaded)).find(w => !holds(w, w.reads.flatMap(call.value))).map(_.id)

  private def holds(w: Assumes, values: List[Any]): Boolean =
    held.get.get(w.id).exists(same(_, values)) || checked(w, values)

  /** Checked now, and kept as holding of `values` when it holds. */
  private def checked(w: Assumes, values: List[Any]): Boolean =
    val ok = w.holds(Env.inForce)
    if ok then
      val _ = held.updateAndGet(_.updated(w.id, values))
    ok

  private def same(xs: List[Any], ys: List[Any]): Boolean = xs.corresponds(ys) {
    case (x: AnyRef, y: AnyRef) => x eq y
    case (x, y)                 => x == y
  }

object AssumptionWatch:
  /** A watch over assumptions that hold of the values wired, or the first that does not. */
  def of(watched: List[Assumes], values: Map[SymbolName, () => Any]): Either[NodeId, AssumptionWatch] =
    watched.find(w => !Values.within(values)(w.holds(Env.inForce))).map(_.id).toLeft(AssumptionWatch(watched))
