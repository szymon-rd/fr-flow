package frflow.proof.whole

import cats.data.NonEmptyList
import frflow.core.analysis.resolution.{Constrained, Resolved}
import frflow.core.consistency.Consistency
import frflow.core.example.Example
import frflow.core.expr.Exprs
import frflow.proof.obligation.{Discharge, Hyp, Obligation, ObligationName, Prop}

/** Each example checked against the claims (owner §18), `example_<set>_<i>`: for every meaning of the Definitions and
  * Declarations it mentions, the statements constraining them, and those constraining what the code standing in it
  * leaves open (keycloak's `record`, which `storeKeepsState` says), give its fact. Tried within a budget: an example
  * the claims do not decide is reported, and nothing else depends on it. An example giving values to provided
  * Definitions is checked against the code only (its values as hypotheses: not planned). The statements at the
  * bottom come first: what the code is held to, in its own terms (`grantWhenNoOverlap` before `grantWhenFree`, which
  * its step gives), is what FrFlow's automation decides an example by. A rule is no hypothesis: Lean has it of every
  * value as a guard, and its claim says nothing (`NodeModules`). Each is tried with its opposite,
  * `example_<set>_<i>_opposite` (today's `eval_<i>_opposite`): the same statements giving the fact's negation, which
  * Lean shows only when the claims contradict the example.
  */
object ExampleGoals:
  val Heartbeats: Int = 20000

  /** In the order of their names (`example_<set>_<i>`), whatever order the sets are read in: Lean's automation can
    * decide a try near its budget differently after other theorems, so one order makes one outcome.
    */
  def of(r: Resolved, examples: List[Example]): List[Obligation] =
    examples.filter(_.givens.isEmpty).sortBy(e => (e.of, e.at)).flatMap(goals(r, _))

  private def goals(r: Resolved, e: Example): List[Obligation] =
    val about = Exprs.mentions(e.fact.value).symbols
    val reached = about.flatMap(Consistency.reach(r.theory, _)).distinct
    val hyps = (about ++ reached).flatMap(Constrained.statements(r.theory, _)).distinct
      .filter(n => r.theory.node(n).exists(s => s.statement.stated && !s.statement.rule))
      .sortBy(r.theory.refinement.parts(_).nonEmpty)
    def stated(fact: Prop) =
      Prop.ForEvery(about, NonEmptyList.fromList(hyps).fold(fact)(hs => Prop.Implies(Hyp.parts(hs.toList), fact)))
    val fact = Prop.Formula(e.fact, Stands.of(r, about))
    List(
      Obligation(ObligationName.Example(e.of, e.at), stated(fact), Discharge.Attempt(Heartbeats),
        s"${e.name}: what the claims say gives it."),
      Obligation(ObligationName.ExampleOpposite(e.of, e.at), stated(Prop.Not(fact)), Discharge.Attempt(Heartbeats),
        s"${e.name}: what the claims say contradicts it."))
