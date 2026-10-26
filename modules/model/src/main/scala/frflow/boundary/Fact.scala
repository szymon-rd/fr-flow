package frflow
package boundary

/** A fact of how the system is run, stated of a store, as an assumption's formula: what FrFlow cannot see from the
  * code, so the developer decides it. In Lean it says nothing (`True`); FrFlow reads it where it matters: an `always`
  * claim about the store holds of its start (`initially`, proven to give the claim's rule), is kept by the programs
  * that write it (`writtenOnlyBy`), and holds between runs (`changedOneRunAtATime`).
  */
final class Fact private[frflow] (val store: StateModel[?], val says: FactKind) extends frflow.term.Term[Boolean](
  Tree.Lit(true, summon[LeanType[Boolean]]), summon[LeanType[Boolean]])

object Fact:
  extension [S](store: StateModel[S])
    /** What the store holds when the system starts: `stored.initially(held => held.pairwise(apart))`. */
    def initially(state: Term[S] => Term[Boolean]): Term[Boolean] =
      Fact(store, FactKind.Initially(frflow.term.Term.quant(all = true, state, List(store.stateType)).termTree))
    /** Only these programs change the store: `stored.writtenOnlyBy(book)`. */
    def writtenOnlyBy(programs: Param[?]*): Term[Boolean] = Fact(store, FactKind.WrittenOnlyBy(programs.toList))
    /** One run changes the store at a time: `stored.changedOneRunAtATime`. */
    def changedOneRunAtATime: Term[Boolean] = Fact(store, FactKind.OneRunAtATime)
