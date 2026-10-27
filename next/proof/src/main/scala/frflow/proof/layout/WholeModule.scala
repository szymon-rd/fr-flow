package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.name.KbName
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerObligation, LowerProp, LowerWitness}
import frflow.proof.obligation.{Discharge, Obligation}
import frflow.proof.terms.TermTable

/** `Whole.lean`: what is asked of the theory as a whole (`Joint`, `ExampleGoals`), each statement in `namespace
  * Obl`, and the theorem of each one FrFlow's witnesses meet (`frflow_witness`) or its automation proves
  * (`frflow_auto`). A statement nothing witnesses is stated only: it shows "consistency not proven" (or "not shown")
  * until the developer's proof file proves it; an example is a try, in the checks module beside it.
  */
final class WholeModule(props: LowerProp, witness: LowerWitness):
  def of(kb: KbName, imports: List[ModuleName], obligations: List[Obligation]): LeanModule =
    LeanModule(Layout(kb).whole, imports, Preamble.generated, Names.path(kb.value, "Whole"), Nil,
      obligations.map(LowerObligation(props)(_)) ++ obligations.collect {
        case o @ Obligation(_, _, Discharge.Witnessed(by), _) => witness(o, by)
        case Obligation(n, _, Discharge.Auto, _)              =>
          val name = LowerObligation.name(n)
          Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)),
            Proof.Tactics(List("frflow_auto")), Break.SameLine)
      })

object WholeModule:
  /** Over the knowledge base's lowering environment, importing what its statements name. */
  def of(r: Resolved, table: TermTable, obligations: List[Obligation]): LeanModule =
    of(Lowering(r, table), obligations)

  def of(l: Lowering, obligations: List[Obligation]): LeanModule =
    Imports.onto(l, WholeModule(l.props, LowerWitness(l.env, l.naming)).of(l.kb, Nil, obligations))

  /** `Whole/Checks.lean`: each example tried against the claims within its budget, by FrFlow's automation. */
  def checks(l: Lowering, obligations: List[Obligation]): Option[LeanModule] =
    val tried = obligations.collect { case o @ Obligation(_, _, Discharge.Attempt(h), _) =>
      val name = LowerObligation.name(o.name)
      Decl.Budgeted(h, Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)),
        Proof.Tactics(List("frflow_auto")), Break.SameLine))
    }
    Option.when(tried.nonEmpty)(LeanModule(l.layout.wholeChecks, List(l.layout.whole), Preamble.generated,
      Names.path(l.kb.value, "Whole", "Checks"), Nil, tried))
