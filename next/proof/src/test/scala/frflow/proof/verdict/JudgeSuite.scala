package frflow.proof.verdict

import frflow.core.name.NodeId
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, TryKind}
import frflow.proof.reading.{Elaboration, NotAllowed, ProofFile}

/** The judges, each on what Lean gave at its step: the model, the lemmas, a proof file, what must hold, a try, the
  * theory as a whole, and the node's check that got through.
  */
class JudgeSuite extends munit.FunSuite:
  private val file = "FrFlowGen/K/N/Checks.lean"
  private val source = """namespace K.N.Checks
    |
    |theorem cover_book : Obl.cover_book := by
    |  frflow_auto
    |
    |theorem clash : Obl.clash := by
    |  frflow_auto
    |
    |theorem made_x : True := by
    |  trivial
    |
    |end K.N.Checks
    |""".stripMargin
  private val failing = s"error: $file:7:2: frflow_auto found no proof"
  private def run(output: String) = Elaboration(source, output, file)
  private val (cover, clash) = (ObligationName.Cover("book"), ObligationName.Tried(TryKind.Clash))

  test("the model: built, broken, or Lean timed out") {
    assertEquals(Judge.model(ProverRun.Built("")), None)
    assertEquals(Judge.model(ProverRun.TimedOut("")).map(_.status), Some(CheckStatus.Timeout))
    assertEquals(Judge.model(ProverRun.Failed(s"error: $file:1:0: unknown")).map(j => (j.status, j.findings.size)),
      Some((CheckStatus.ModelError, 1)))
  }

  test("the lemmas: what a proof file may contain, no lemmas imported, built without sorry; one that does not build " +
    "leaves the importer open, not failed") {
    val lemmas = ProofFile(NodeId("Lemmas"), "theorem t : True := trivial\n")
    assertEquals(Judge.lemmas(lemmas, ProverRun.Built("")), None)
    assertEquals(Judge.lemmas(lemmas, ProverRun.Built("declaration uses 'sorry'")).map(_.status),
      Some(CheckStatus.Open))
    assertEquals(Judge.lemmas(lemmas, ProverRun.Failed(s"error: $file:1:0: omega could not prove the goal"))
      .map(j => (j.status, j.findings.size)), Some((CheckStatus.Open, 1)))
    val importing = ProofFile(NodeId("Lemmas"), "import Proofs.K.Lemmas\n")
    assertEquals(Judge.lemmas(importing, ProverRun.Built("")).map(_.findings),
      Some(List(Finding.ProofNotAllowed(List(1 -> NotAllowed.LemmaImport("Proofs.K.Lemmas"))))))
  }

  test("a proof file: refused for what it may not contain") {
    assertEquals(Judge.proofFile(ProofFile(NodeId("N"), "theorem impl : Obl.impl := by\n  native_decide\n")).map(
      _.findings), Some(List(Finding.ProofNotAllowed(List(2 -> NotAllowed.NativeDecide)))))
  }

  test("what must hold: proven, open with Lean's errors, missing, or failed for stating something else") {
    assertEquals(Judge.required(cover, run("")).status, ObligationStatus.Proven)
    assertEquals(Judge.required(clash, run(failing)).status, ObligationStatus.Open)
    assertEquals(Judge.required(clash, run(failing)).messages.map(_.line), List(7))
    assertEquals(Judge.required(ObligationName.Impl, run("")).status, ObligationStatus.Open)
    assertEquals(Judge.required(ObligationName.Made("x"), run("")).status, ObligationStatus.Failed)
  }

  test("a try: shown when Lean proves it, not shown otherwise") {
    assertEquals(Judge.tried(clash, run("")).status, ObligationStatus.Shown)
    assertEquals(Judge.tried(clash, run(failing)).status, ObligationStatus.NotShown)
  }

  test("the theory as a whole: an example is a try, a consistency group what must hold") {
    val example = Obligation(clash, Prop.False, Discharge.Attempt(100), "")
    val group = Obligation(cover, Prop.False, Discharge.Unwitnessed, "")
    assertEquals(Judge.whole(example, run(failing)).status, ObligationStatus.NotShown)
    assertEquals(Judge.whole(group, run("")).status, ObligationStatus.Proven)
  }

  test("a node's check: refuted by a fatal try shown, failed, open, waiting for its parts, or proven") {
    def r(o: ObligationName, s: ObligationStatus) = Result(o, s, Nil)
    val proven = r(ObligationName.Complete, ObligationStatus.Proven)
    assertEquals(Judge.node(List(proven, r(clash, ObligationStatus.Shown)), Nil, Nil).findings,
      List(Finding.Refuted(List(TryKind.Clash))))
    assertEquals(Judge.node(List(proven), List("sorryAx"), Nil).findings,
      List(Finding.DisallowedAxioms(List("sorryAx"))))
    assertEquals(Judge.node(List(r(cover, ObligationStatus.Failed)), Nil, Nil).status, CheckStatus.Failed)
    assertEquals(Judge.node(List(proven, r(cover, ObligationStatus.Open)), Nil, Nil).status, CheckStatus.Open)
    assertEquals(Judge.node(List(proven), Nil, List(CheckStatus.Open)).status, CheckStatus.Waiting)
    val parts = List(CheckStatus.Proven)
    assertEquals(Judge.node(List(proven, r(clash, ObligationStatus.NotShown)), List("propext"), parts).status,
      CheckStatus.Proven)
  }
