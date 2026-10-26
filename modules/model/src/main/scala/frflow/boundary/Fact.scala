package frflow
package boundary

/** A fact of how the system is run, stated of a store (or of the inputs a program is called with), as an assumption's
  * formula: what FrFlow cannot see from the code, so the developer decides it. In Lean it says nothing (`True`);
  * FrFlow reads it where it matters: an `always` claim about the store holds of its start (`initially`, proven to give
  * the claim's rule, or `startsMeetingItsRules`), is kept by the programs that write it (`writtenOnlyBy`), and holds
  * between runs (`changedOneRunAtATime`); an `always` claim about a type holds of the values entering from outside
  * (`calledWithInputsMeetingTheirRules`).
  */
final class Fact private[frflow] (val store: Option[StateModel[?]], val says: FactKind)
    extends frflow.term.Term[Boolean](Tree.Lit(true, summon[LeanType[Boolean]]), summon[LeanType[Boolean]])

object Fact:
  extension [S](store: StateModel[S])
    /** What the store holds when the system starts: `bookings.initially(held => held.isEmpty)`. */
    def initially(state: Term[S] => Term[Boolean]): Term[Boolean] =
      Fact(Some(store), FactKind.Initially(frflow.term.Term.quant(all = true, state, List(store.stateType)).termTree))
    /** The store starts in a state meeting what always holds of it: `bookings.startsMeetingItsRules`. */
    def startsMeetingItsRules: Term[Boolean] = Fact(Some(store), FactKind.StartsMeetingItsRules)
    /** Only these programs change the store: `bookings.writtenOnlyBy(book)`. */
    def writtenOnlyBy(programs: Param[?]*): Term[Boolean] = Fact(Some(store), FactKind.WrittenOnlyBy(programs.toList))
    /** One run changes the store at a time: `bookings.changedOneRunAtATime`. */
    def changedOneRunAtATime: Term[Boolean] = Fact(Some(store), FactKind.OneRunAtATime)

  extension (program: Param[?])
    /** The program is called from outside only with inputs meeting what always holds of their types:
      * `book.calledWithInputsMeetingTheirRules`.
      */
    def calledWithInputsMeetingTheirRules: Term[Boolean] =
      Fact(None, FactKind.CalledWithInputsMeetingTheirRules(program))
