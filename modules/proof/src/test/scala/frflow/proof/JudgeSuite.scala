package frflow.proof

import frflow.core.name.NodeId
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, TryKind}
import frflow.proof.reading.{Elaboration, NotAllowed, ProofFile, RocqReport}
import frflow.proof.verdict.*

/** The judges, each on what Rocq gave at its step: the model, the lemmas, a proof file, what must hold, a try, the
  * theory as a whole, and the node's check that got through.
  */
class JudgeSuite extends munit.FunSuite:
  private val file = "FrFlowGen/K/N/Checks.v"
  private val source = """Require Export FrFlowGen.K.N.Spec.
    |
    |Lemma N_Checks_made_book : N_Obl_made_book.
    |Proof. timeout 20 (frflow_auto). Qed.
    |
    |Lemma N_Checks_clash : N_Obl_clash.
    |Proof. timeout 20 (frflow_auto). Qed.
    |
    |Lemma N_Checks_made_x : True.
    |Proof. auto. Qed.
    |""".stripMargin
  private def report(open: (String, String)*): String =
    RocqReport.print(List(RocqReport.File(file, open.toMap, Map.empty, None)))
  private val failing = report("N_Checks_clash" -> "frflow_auto found no proof")
  private def run(output: String) = Elaboration(source, output, file, List("K", "N", "Checks"))
  private val (cover, clash) = (ObligationName.Made("book"), ObligationName.Tried(TryKind.Clash))
  private val unread = RocqReport.print(List(RocqReport.File(file, Map.empty, Map.empty, Some("Syntax error."))))

  test("the model: built, broken, or Rocq timed out") {
    assertEquals(Judge.model(ProverRun.Built(report())), None)
    assertEquals(Judge.model(ProverRun.TimedOut("")).map(_.status), Some(CheckStatus.Timeout))
    assertEquals(Judge.model(ProverRun.Failed(unread)).map(j => (j.status, j.findings)),
      Some((CheckStatus.ModelError, List(Finding.ModelDoesNotBuild(List(
        frflow.proof.reading.Diagnostic(file, 0, true, "Syntax error.")))))))
  }

  test("the lemmas: what a proof file may contain, no lemmas imported, every one proven; one that is not leaves " +
    "the importer open, not failed") {
    val lemmas = ProofFile(NodeId("Lemmas"), "Lemma t : True.\nProof.\n  auto.\nQed.\n")
    assertEquals(Judge.lemmas(lemmas, ProverRun.Built(report())), None)
    assertEquals(Judge.lemmas(lemmas, ProverRun.Built(failing)).map(_.status), Some(CheckStatus.Open))
    assertEquals(Judge.lemmas(lemmas, ProverRun.Failed(failing)).map(j => (j.status, j.findings.size)),
      Some((CheckStatus.Open, 1)))
    val importing = ProofFile(NodeId("Lemmas"), "Require Export Proofs.K.Lemmas.\n")
    assertEquals(Judge.lemmas(importing, ProverRun.Built(report())).map(_.findings),
      Some(List(Finding.ProofNotAllowed(List(1 -> NotAllowed.LemmaImport("Proofs.K.Lemmas"))))))
  }

  test("a proof file: refused for what it may not contain") {
    assertEquals(Judge.proofFile(ProofFile(NodeId("N"), "Lemma N_Proofs_impl : N_Obl_impl.\nProof.\nAdmitted.\n"))
      .map(_.findings), Some(List(Finding.ProofNotAllowed(List(3 -> NotAllowed.Command("Admitted."),
        3 -> NotAllowed.Admit)))))
  }

  test("what must hold: proven, open with what Rocq said, missing, or failed for stating something else") {
    assertEquals(Judge.required(cover, run(report())).status, ObligationStatus.Proven)
    assertEquals(Judge.required(clash, run(failing)).status, ObligationStatus.Open)
    assertEquals(Judge.required(clash, run(failing)).messages.map(m => (m.line, m.message)),
      List((6, "frflow_auto found no proof")))
    assertEquals(Judge.required(ObligationName.Impl, run(report())).status, ObligationStatus.Open)
    assertEquals(Judge.required(ObligationName.Made("x"), run(report())).status, ObligationStatus.Failed)
  }

  test("a try: shown when Rocq proves it, not shown otherwise") {
    assertEquals(Judge.tried(clash, run(report())).status, ObligationStatus.Shown)
    assertEquals(Judge.tried(clash, run(failing)).status, ObligationStatus.NotShown)
    assertEquals(Judge.tried(clash, run("")).status, ObligationStatus.NotShown)
  }

  test("the theory as a whole: an example is a try, a consistency group what must hold") {
    val example = Obligation(clash, Prop.False, Discharge.Attempt(100), "")
    val group = Obligation(cover, Prop.False, Discharge.Unwitnessed, "")
    assertEquals(Judge.whole(example, run(failing)).status, ObligationStatus.NotShown)
    assertEquals(Judge.whole(group, run(report())).status, ObligationStatus.Proven)
  }

  test("a node's check: refuted by a fatal try shown, failed, open, waiting for its parts, or proven") {
    def r(o: ObligationName, s: ObligationStatus) = Result(o, s, Nil)
    val proven = r(ObligationName.Complete, ObligationStatus.Proven)
    assertEquals(Judge.node(List(proven, r(clash, ObligationStatus.Shown)), Nil, Nil).findings,
      List(Finding.Refuted(List(TryKind.Clash))))
    assertEquals(Judge.node(List(proven), List("N_Proofs_helper"), Nil).findings,
      List(Finding.DisallowedAxioms(List("N_Proofs_helper"))))
    assertEquals(Judge.node(List(r(cover, ObligationStatus.Failed)), Nil, Nil).status, CheckStatus.Failed)
    assertEquals(Judge.node(List(proven, r(cover, ObligationStatus.Open)), Nil, Nil).status, CheckStatus.Open)
    assertEquals(Judge.node(List(proven), Nil, List(CheckStatus.Open)).status, CheckStatus.Waiting)
    val parts = List(CheckStatus.Proven)
    assertEquals(Judge.node(List(proven, r(clash, ObligationStatus.NotShown)), List("classic"), parts).status,
      CheckStatus.Proven)
  }
