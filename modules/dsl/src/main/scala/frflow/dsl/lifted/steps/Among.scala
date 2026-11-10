package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.{LeanType, Lift, Term, Terms, TermSyntax}
import frflow.dsl.vocab.Definition

/** What other calls do between two steps of one call, as the interleaved reading writes it (`StepReader`). */
object Among:
  /** What the schedule says other calls left before step `k` (`between`); nothing said, the state the call last
    * saw (`before`).
    */
  def left[S](before: Term[S], between: Term[Map[BigInt, S]], k: BigInt): Term[S] =
    LiftOps.valueOr(between, Lift.constant(k), before)

  /** The state a step starts from: what other calls left before it (`left`), when the rely admits it after the
    * state the call last saw (`before`); else that state, the others having done nothing. So every schedule is one
    * the rely allows, and a claim over every schedule is one over every interleaving.
    */
  def admitted[A: LeanType, S: LeanType](before: Term[S], left: Term[S])(
      rely: Definition[(A, S, S) => Boolean], input: Term[A]): Term[S] =
    Terms.let(left, "seen", (seen: Term[S]) => TermSyntax.when(rely(input, before, seen))(seen).otherwise(before))
