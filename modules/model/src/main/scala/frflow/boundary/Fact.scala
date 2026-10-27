package frflow
package boundary

/** A fact of how the system is run, stated of a store, as an assumption's formula: what FrFlow cannot see from the
  * code, so the developer decides it. In Lean it says nothing (`True`); FrFlow reads it where it matters: an `always`
  * claim about the store holds of its start (`initially`, proven to give the claim's rule, or `startsSatisfying`,
  * naming the claim), is kept by the programs that write it (`writtenOnlyBy`), and holds between runs
  * (`changedOneRunAtATime`). What comes from outside is not a fact: it has a type of its own, and what it meets is
  * an assumption `always` of that type.
  */
final class Fact private[frflow] (val store: Option[StateModel[?]], val says: FactKind)
    extends frflow.term.Term[Boolean](Tree.Lit(true, summon[LeanType[Boolean]]), summon[LeanType[Boolean]])

object Fact:
  extension [S](store: StateModel[S])
    /** What the store holds when the system starts: `storedBookings.initially(held => held.isEmpty)`. */
    def initially(state: Term[S] => Term[Boolean]): Term[Boolean] =
      Fact(Some(store), FactKind.Initially(frflow.term.Term.quant(all = true, state, List(store.stateType)).termTree))
    /** The store starts in a state satisfying an `always` claim about it:
      * `storedBookings.startsSatisfying(neverOverlap)`. The claim rests on this fact without naming it (no
      * `.assuming`): it is declared first, and the fact names it.
      */
    def startsSatisfying(claim: Node[?]): Term[Boolean] =
      require(claim != null, "startsSatisfying names a claim declared after it: declare the always claim first")
      Fact(Some(store), FactKind.StartsSatisfying(claim))
    /** Only these programs change the store: `storedBookings.writtenOnlyBy(book)`. */
    def writtenOnlyBy(programs: Param[?]*): Term[Boolean] = Fact(Some(store), FactKind.WrittenOnlyBy(programs.toList))
    /** One run changes the store at a time: `storedBookings.changedOneRunAtATime`. */
    def changedOneRunAtATime: Term[Boolean] = Fact(Some(store), FactKind.OneRunAtATime)
