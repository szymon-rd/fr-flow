package keycloak

import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.project.pipeline.Analysis
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, ObligationName}
import frflow.proof.reading.ProofFile

/** The developer proves what is asked of the whole theory (owner §39): the statements stand in `Whole/Spec.lean`; a
  * theorem of `Proofs/Keycloak/Whole.lean` makes its obligation authored, FrFlow's own module then stating it no
  * more, and the axioms of each proof are audited beside it.
  */
class WholeProofSuite extends munit.FunSuite:
  private val bare = Projects.bare(Projects.elaborated(knowledge))
  private val proof = ProofFile(NodeId("Whole"),
    "import FrFlowGen.Keycloak.Whole.Spec\n\nnamespace Keycloak.Whole.Proofs\n\n" +
      "theorem consistent_5 : Obl.consistent_5 := by\n  trivial\n\nend Keycloak.Whole.Proofs\n")
  private val proven = Analysis(bare.valid,
    bare.inputs.copy(lean = bare.inputs.lean.copy(proofs = Map(NodeId("Whole") -> proof))), bare.computed)

  private def module(on: Analysis, name: String): Option[String] =
    on.modules.find(_.name.dotted == s"FrFlowGen.Keycloak.$name").map(Print.module)

  test("a theorem of the developer's whole proof file makes its obligation authored; the others stay FrFlow's") {
    val discharges = proven.whole.map(o => o.name -> o.discharge).toMap
    assertEquals(discharges(ObligationName.Consistent(5)), Discharge.Authored)
    assertNotEquals(discharges(ObligationName.Consistent(0)), Discharge.Authored)
    assertEquals(proven.wholeProof, Some(proof))
  }

  test("every statement stands in Whole/Spec; FrFlow's module proves none the developer does; the audit prints it") {
    val spec = module(proven, "Whole.Spec").getOrElse(fail("no statements"))
    assert(spec.contains("def consistent_5 ") && spec.contains("def consistent_0 "), spec)
    val whole = module(proven, "Whole").getOrElse(fail("no whole module"))
    assert(!whole.contains("theorem consistent_5") && whole.contains("theorem consistent_0"), whole)
    assertEquals(module(proven, "Whole.Audit").map(_.contains("#print axioms Keycloak.Whole.Proofs.consistent_5")),
      Some(true))
    assertEquals(module(bare, "Whole.Audit"), None)
  }
