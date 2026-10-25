package frflow
package boundary

/** What a boundary does, as the proofs see it: an implementation of its trait over a state `S`, read and changed
  * with `state.get`, `state.set` and `state.update`. Deterministic, never failing, with the boundary to itself
  * during a run: what is unknown (a clock's readings) goes into the state.
  */
trait StateModel[S](using private[frflow] val stateType: LeanType[S]):
  protected final val state: State[S] = State(this)
  /** Lean's namespace of the model's operations. */
  private[frflow] def lean: String = Names.ident(getClass.getSimpleName.stripSuffix("$"))
  /** The boundary's trait this models: the one interface of the model's whose methods are flows. */
  private[frflow] lazy val boundaryTrait: Class[?] =
    getClass.getInterfaces.find(i => i.getMethods.exists(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)))
      .getOrElse(throw IllegalStateException(s"FrFlow: $lean implements no boundary (a trait of operations returning flows)"))
  /** Its field in Lean's `World`: the trait's name, lowered (`database`). */
  private[frflow] def field: String = Names.ident(boundaryTrait.getSimpleName.head.toLower.toString + boundaryTrait.getSimpleName.tail)
