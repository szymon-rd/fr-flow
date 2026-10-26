package frflow
package boundary

import frflow.types.Shape

/** A fact of how the system is run, stated of a store (or of the inputs a program is called with), as an assumption's
  * formula: what FrFlow cannot see from the code, so the developer decides it. In Lean it says nothing (`True`);
  * FrFlow reads it where it matters: an `always` claim about the store holds of its start (`initially`, proven to give
  * the claim's rule, or `startsSatisfying`, naming the claim), is kept by the programs that write it
  * (`writtenOnlyBy`), and holds between runs (`changedOneRunAtATime`); an `always` claim about a type holds of the
  * values entering from outside (`calledOnlyWith`, proven to give the claim's rule).
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

  extension [A, R](program: Param[A => R])
    /** The program is called from outside only on inputs meeting the condition:
      * `book.calledOnlyWith(request => request.start < request.end)`.
      */
    def calledOnlyWith(condition: Term[A] => Term[Boolean]): Term[Boolean] =
      val input = program.termType.shape match
        case Shape.FnOf(List(a), _) => a
        case _ => throw IllegalArgumentException(s"FrFlow: ${program.name}.calledOnlyWith: a program of one input")
      Fact(None, FactKind.CalledOnlyWith(program, frflow.term.Term.quant(all = true, condition, List(input)).termTree))
