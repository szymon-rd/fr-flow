package frflow.runtime

import frflow.dsl.{Implementation, Operation}

/** Result of submitting an operation. */
enum Outcome[+S]:
  /** The guard held and the effect was applied. */
  case Accepted(state: S)
  /** A `check` clause of the guard failed; the state is unchanged. */
  case Rejected(operation: String)

  def accepted: Boolean = this.isInstanceOf[Accepted[?]]

/** Runs an implementation layer.
  *
  * Executes the same Scala functions that FrFlow translated to Lean and proved to
  * refine the layers above: an operation is applied only when its `check`
  * clauses hold. `assume` clauses are environment assumptions and are not
  * evaluated. Submissions are serialized, so each one is one atomic step of the
  * verified machine.
  */
final class Service[S](val layer: Implementation[S, ?]):
  private val ops = layer.operations.toSet[Operation[S, ?]]
  private var current: S =
    layer.initialState.getOrElse(throw IllegalStateException(s"${layer.id} declares no initial state")).value

  def state: S = synchronized(current)

  def submit[P](op: Operation[S, P], params: P): Outcome[S] = synchronized {
    require(ops.contains(op), s"$op is not an operation of ${layer.id}")
    if op.enabled(current, params) then
      current = op(current, params)
      Outcome.Accepted(current)
    else Outcome.Rejected(op.name)
  }

object Service:
  def apply[S](layer: Implementation[S, ?]): Service[S] = new Service(layer)

  /** One step of `layer` from `state`, without a service: the pure transition function. */
  def step[S, P](op: Operation[S, P], state: S, params: P): Outcome[S] =
    if op.enabled(state, params) then Outcome.Accepted(op(state, params)) else Outcome.Rejected(op.name)
