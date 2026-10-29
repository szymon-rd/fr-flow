package keycloak

import cats.effect.IO
import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.project.check.WholeChecker
import frflow.eval.run.OnCode
import frflow.project.pipeline.{Analysis, Computed}
import frflow.project.port.memory.ScriptedLake
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, ObligationName}
import frflow.proof.reading.ProofFile
import frflow.proof.verdict.{ObligationStatus, ProverRun}

/** The developer proves what is asked of the whole theory (owner §39): the statements stand in `Whole/Spec.lean`; a
  * theorem of `Proofs/Keycloak/Whole.lean` makes its obligation authored, FrFlow's own module then stating it no
  * more, and the axioms of each proof are audited beside it.
  */
class WholeProofSuite extends munit.CatsEffectSuite:
  private val bare = Projects.bare(Projects.elaborated(knowledge))
  private val proof = ProofFile(NodeId("Whole"),
    "import FrFlowGen.Keycloak.Whole.Spec\n\nnamespace Keycloak.Whole.Proofs\n\n" +
      "theorem consistent_3 : Obl.consistent_3 := by\n  trivial\n\nend Keycloak.Whole.Proofs\n")
  private def proving(f: ProofFile): Analysis = Analysis(bare.valid,
    bare.inputs.copy(lean = bare.inputs.lean.copy(proofs = Map(NodeId("Whole") -> f))), bare.computed)
  private val proven = proving(proof)

  private def module(on: Analysis, name: String): Option[String] =
    on.modules.find(_.name.dotted == s"FrFlowGen.Keycloak.$name").map(Print.module)

  test("a theorem of the developer's whole proof file makes its obligation authored; the others stay FrFlow's") {
    val discharges = proven.whole.map(o => o.name -> o.discharge).toMap
    assertEquals(discharges(ObligationName.Consistent(3)), Discharge.Authored)
    assertNotEquals(discharges(ObligationName.Consistent(0)), Discharge.Authored)
    assertEquals(proven.wholeProof, Some(proof))
  }

  test("every statement stands in Whole/Spec; FrFlow's module proves none the developer does; the audit prints it") {
    val spec = module(proven, "Whole.Spec").getOrElse(fail("no statements"))
    assert(spec.contains("def consistent_3 ") && spec.contains("def consistent_0 "), spec)
    val whole = module(proven, "Whole").getOrElse(fail("no whole module"))
    assert(!whole.contains("theorem consistent_3") && whole.contains("theorem consistent_0"), whole)
    assertEquals(module(proven, "Whole.Audit").map(_.contains("#print axioms Keycloak.Whole.Proofs.consistent_3")),
      Some(true))
    assertEquals(module(bare, "Whole.Audit"), None)
  }

  test("a whole proof file holding what it may not fails what it proves, though Lean accepts it (owner §39)") {
    def judged(f: ProofFile) =
      val a = proving(f)
      for
        lake <- ScriptedLake[IO](m => a.modules.find(_.name == m).fold(ProverRun.Built(""))(
          ScriptedLake.building(_, Set.empty)), installed = true)
        out  <- WholeChecker[IO](lake)(a)
      yield out.toList.flatMap(_.results).find(_.name == ObligationName.Consistent(3)).map(_.status)
    val cheating = ProofFile(NodeId("Whole"), proof.source.replace("theorem consistent_3",
      "axiom cheat : False\n\ntheorem consistent_3"))
    for
      fair  <- judged(proof)
      cheat <- judged(cheating)
    yield assertEquals((fair, cheat), (Some(ObligationStatus.Proven), Some(ObligationStatus.Failed)))
  }

  test("a request example takes what storeKeepsState says of the record the step's code leaves open") {
    val examples = RequestExamples().elaborated.fold(e => fail(e.toString), identity)
    val a = Analysis(bare.valid, bare.inputs, Computed(examples.map(_ -> OnCode.Holds), Map.empty))
    val spec = module(a, "Whole.Spec").getOrElse(fail("no statements"))
    val first = spec.linesIterator.dropWhile(!_.contains("def example_0 ")).slice(1, 2).mkString
    assert(first.contains("(Keycloak.storeKeepsState.claim record)") && first.contains("(Keycloak.handle record "),
      first)
  }
