package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.name.KbName
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerObligation, LowerProp, LowerWitness}
import frflow.proof.obligation.{Discharge, Obligation}
import frflow.proof.terms.TermTable

/** What is asked of the theory as a whole (`Joint`, `ExampleGoals`): `Whole/Spec.lean`, each statement in `namespace
  * Obl`; and `Whole.lean`, the theorem of each one FrFlow's witnesses meet (`frflow_witness`) or its automation
  * proves (`frflow_auto`), each with its axioms audited. A statement nothing witnesses is stated only: it shows
  * "consistency not proven" (or "not shown") until the developer's proof file (`Proofs/<Model>/Whole.lean`, which
  * imports the statements alone, so a witness Lean refuses there stops none of its proofs) proves it; an example is a
  * try, in the checks module beside it.
  */
final class WholeModule(props: LowerProp, witness: LowerWitness):
  def statements(kb: KbName, obligations: List[Obligation]): LeanModule =
    LeanModule(Layout(kb).wholeSpec, Nil, Preamble.generated, Names.path(kb.value, "Whole"), Nil,
      obligations.map(LowerObligation(props)(_)))

  def of(kb: KbName, obligations: List[Obligation]): LeanModule =
    LeanModule(Layout(kb).whole, Nil, Preamble.generated, Names.path(kb.value, "Whole"), Nil,
      obligations.collect {
        case o @ Obligation(_, _, Discharge.Witnessed(by), _) => List(witness(o, by), audit(kb, o))
        case o @ Obligation(n, _, Discharge.Auto, _)          =>
          val name = LowerObligation.name(n)
          List(Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)),
            Proof.Tactics(List("frflow_auto")), Break.SameLine), audit(kb, o))
      }.flatten)

  /** `#print axioms` of a theorem met here: what its proof rests on, audited as a node's proofs are. */
  private def audit(kb: KbName, o: Obligation): Decl =
    Decl.PrintAxioms(Names.path(kb.value, "Whole", LowerObligation.name(o.name).text))

object WholeModule:
  /** Over the FrModel's lowering environment, importing what its statements name: the statements, and FrFlow's own
    * theorems of them.
    */
  def of(r: Resolved, table: TermTable, obligations: List[Obligation]): List[LeanModule] =
    of(Lowering(r, table), obligations)

  def of(l: Lowering, obligations: List[Obligation]): List[LeanModule] =
    val made = WholeModule(l.props, LowerWitness(l.env, l.naming, l.props))
    val whole = Imports.onto(l, made.of(l.kb, obligations))
    List(Imports.onto(l, made.statements(l.kb, obligations)),
      whole.copy(imports = (l.layout.wholeSpec :: whole.imports).distinct))

  /** `Whole/Audit.lean`: what each of the developer's proofs of the theory's obligations rests on (`#print axioms`,
    * which a proof file may not hold).
    */
  def audit(l: Lowering, obligations: List[Obligation]): Option[LeanModule] =
    val authored = obligations.collect { case o @ Obligation(_, _, Discharge.Authored, _) =>
      Decl.PrintAxioms(Names.path(l.kb.value, "Whole", "Proofs", LowerObligation.name(o.name).text))
    }
    Option.when(authored.nonEmpty)(LeanModule(l.layout.wholeAudit, List(l.layout.wholeProofs), Preamble.generated,
      Names.path(l.kb.value, "Whole", "Audit"), Nil, authored))

  /** `Whole/Checks.lean`: each example tried against the claims within its budget, by FrFlow's automation, over the
    * statements alone (a witness Lean refuses stops no example).
    */
  def checks(l: Lowering, obligations: List[Obligation]): Option[LeanModule] =
    val tried = obligations.collect { case o @ Obligation(_, _, Discharge.Attempt(h), _) =>
      val name = LowerObligation.name(o.name)
      Decl.Budgeted(h, Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)),
        Proof.Tactics(List("frflow_auto")), Break.SameLine))
    }
    Option.when(tried.nonEmpty)(LeanModule(l.layout.wholeChecks, List(l.layout.wholeSpec), Preamble.generated,
      Names.path(l.kb.value, "Whole", "Checks"), Nil, tried))
