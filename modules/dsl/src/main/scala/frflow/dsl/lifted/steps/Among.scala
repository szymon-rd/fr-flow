package frflow.dsl.lifted.steps

import frflow.dsl.lifted.LiftOps
import frflow.dsl.structure.Call
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

  /** What a structure's member did among other calls (`Call.Traces`): each step it took (the structure as the step
    * found it, as it left it), and what the other calls did before each step but the first (the structure as the
    * call last left it, as they left it).
    */
  type Traces[S] = Call.Traces[S]

  def none[S: LeanType]: Term[Traces[S]] = LiftOps.pair(LiftOps.nil[(S, S)], LiftOps.nil[(S, S)])

  /** The traces with a step added. */
  def stepped[S: LeanType](traces: Term[Traces[S]], found: Term[S], left: Term[S]): Term[Traces[S]] =
    LiftOps.pair(TermSyntax.:+(TermSyntax._1(traces))(LiftOps.pair(found, left)), TermSyntax._2(traces))

  /** The traces with what the other calls did before a step added. */
  def moved[S: LeanType](traces: Term[Traces[S]], seen: Term[S], left: Term[S]): Term[Traces[S]] =
    LiftOps.pair(TermSyntax._1(traces), TermSyntax.:+(TermSyntax._2(traces))(LiftOps.pair(seen, left)))

  /** A member that calls no other structure, among other calls: one step, the member run. */
  def atomic[V: LeanType, S: LeanType](state: Term[S], run: Term[(V, S)]): Term[((V, S), Traces[S])] =
    Terms.let(run, "did", (did: Term[(V, S)]) => LiftOps.pair(did,
      LiftOps.pair(LiftOps.cons(LiftOps.pair(state, TermSyntax._2(did)), LiftOps.nil[(S, S)]), LiftOps.nil[(S, S)])))

  /** What a member's reading among other calls gives: its result with the structure after it, and the traces. */
  def ended[V: LeanType, S: LeanType](v: Term[V], state: Term[S], traces: Term[Traces[S]])
      : Term[((V, S), Traces[S])] = LiftOps.pair(LiftOps.pair(v, state), traces)
