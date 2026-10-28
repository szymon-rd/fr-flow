package frflow.proof.whole

import cats.data.NonEmptyList
import frflow.core.analysis.{Constrained, Resolved}
import frflow.core.example.Example
import frflow.core.expr.Exprs
import frflow.proof.obligation.{Discharge, Hyp, Obligation, ObligationName, Prop}

/** Each example checked against the claims (owner §18), `example_<i>`: for every meaning of the Definitions and
  * Declarations it mentions, the statements constraining them give its fact. Tried within a budget: an example the
  * claims do not decide is reported, and nothing else depends on it. An example giving values to provided
  * Definitions is checked against the code only (its values as hypotheses: not planned). The statements at the
  * bottom come first: what the code is held to, in its own terms (`grantWhenNoOverlap` before `grantWhenFree`, which
  * its step gives), is what FrFlow's automation decides an example by. A rule is no hypothesis: Lean has it of every
  * value as a guard, and its claim says nothing (`NodeModules`).
  */
object ExampleGoals:
  val Heartbeats: Int = 20000

  def of(r: Resolved, examples: List[Example]): List[Obligation] = examples.zipWithIndex.collect {
    case (e, i) if e.givens.isEmpty =>
      val about = Exprs.mentions(e.fact.value).symbols
      val hyps = about.flatMap(Constrained.statements(r.theory, _)).distinct
        .filter(n => r.theory.node(n).exists(s => s.statement.stated && !s.statement.rule))
        .sortBy(r.theory.refinement.parts(_).nonEmpty)
      Obligation(ObligationName.Example(i),
        Prop.ForEvery(about, NonEmptyList.fromList(hyps).fold(Prop.Formula(e.fact))(hs =>
          Prop.Implies(Hyp.parts(hs.toList), Prop.Formula(e.fact)))),
        Discharge.Attempt(Heartbeats), s"${e.name}: what the claims say gives it.")
  }
