package frflow.proof

import frflow.core.name.NodeId
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.*

/** Reading a Rocq file and what Rocq said of it: its lemmas with their lines, what it imports and audits, a lemma
  * given up in place, the error Rocq stopped at, what each audit printed, a build's report, each lemma's verdict,
  * and every obligation's name read back.
  */
class ReadingSuite extends munit.FunSuite:
  private val source = """Require Export FrFlowGen.Crm.N.Spec.
    |From FrFlow Require Export Base.
    |
    |(* Lemma hidden : False. *)
    |Lemma N_Checks_made_book : N_Obl_made_book.
    |Proof. timeout 20 (frflow_auto). Qed.
    |
    |Print Assumptions N_Checks_made_book.
    |
    |Lemma N_Checks_unsat :
    |  N_Obl_unsat.
    |Proof.
    |  intros.
    |  frflow_auto.
    |Qed.
    |""".stripMargin
  private val file = "FrFlowGen/Crm/N/Checks.v"
  private val namespace = List("Crm", "N", "Checks")

  test("a file's lemmas, with their lines; a comment states none") {
    assertEquals(RocqSource.lemmas(source), List(Theorem("N_Checks_made_book", "N_Obl_made_book", 5, 6),
      Theorem("N_Checks_unsat", "N_Obl_unsat", 10, 15)))
  }

  test("a lemma with binders is a lemma: what it states is read with them") {
    val shared =
      "Lemma Lemmas_apart (a b : Booking) :\n  ends a -> (apart a b <-> noOverlap a b).\nProof.\n  lia.\nQed.\n"
    assertEquals(RocqSource.lemmas(shared),
      List(Theorem("Lemmas_apart", "(a b : Booking) : ends a -> (apart a b <-> noOverlap a b)", 1, 5)))
    assert(RocqSource.admitted(shared, RocqSource.lemmas(shared).head).exists(_.contains("Proof. Admitted.")))
  }

  test("what a file imports, as Rocq names it, and the lemmas it audits") {
    assertEquals(RocqSource.imports(source), List("FrFlowGen.Crm.N.Spec", "FrFlow.Base"))
    assertEquals(RocqSource.imports("Require Import A.B C.\nRequire Export D.\n"), List("A.B", "C", "D"))
    assertEquals(RocqSource.audited(source), List("N_Checks_made_book"))
  }

  test("a lemma given up keeps every line where it is; one given up already, or with no proof, is none") {
    val lemmas = RocqSource.lemmas(source)
    val givenUp = RocqSource.admitted(source, lemmas(1)).getOrElse(fail("not given up"))
    assertEquals(givenUp.linesIterator.toList.slice(9, 15), List("Lemma N_Checks_unsat :", "  N_Obl_unsat.",
      "Proof. Admitted.", "", "", ""))
    assertEquals(givenUp.linesIterator.size, source.linesIterator.size)
    assertEquals(RocqSource.admitted(givenUp, RocqSource.lemmas(givenUp)(1)), None)
    assert(RocqSource.admitted(source, lemmas.head).exists(_.contains("Proof. Admitted.\n\nPrint Assumptions")))
  }

  test("the error Rocq stopped at, past the warnings before it; what each audit printed") {
    val error = """File "./W.v", line 3, characters 16-19:
      |Warning: Reference old is deprecated. x
      |[deprecated-reference,deprecated,default]
      |File "./FrFlowGen/Crm/N/Checks.v", line 14, characters 2-13:
      |Error: Tactic failure: frflow_auto found no proof.
      |""".stripMargin
    assertEquals(RocqOutput.error(error), Some(14 -> "Tactic failure: frflow_auto found no proof."))
    assertEquals(RocqOutput.error("Error: cannot find library"), None)
    val printed = """Closed under the global context
      |Axioms:
      |classic : forall P : Prop, P \/ ~ P
      |functional_extensionality_dep
      |  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      |    (forall x : A, f x = g x) -> f = g
      |""".stripMargin
    assertEquals(RocqOutput.assumptions(printed), List(Nil, List("classic", "functional_extensionality_dep")))
  }

  private val said = RocqReport.File(file, Map("N_Checks_unsat" -> "Tactic failure:\nno proof."),
    Map("N_Checks_made_book" -> List("classic")), None)

  test("a build's report reads back as written, a message of several lines among it") {
    val files = List(said, RocqReport.File("Proofs/Crm/N.v", Map.empty, Map.empty, Some("Syntax error.")))
    assertEquals(RocqReport.read(RocqReport.print(files)), files)
  }

  test("each lemma's verdict: proven, not accepted with what Rocq said, or in no file Rocq read") {
    val e = Elaboration(source, RocqReport.print(List(said)), file, namespace)
    assertEquals(e.verdict("made_book"), TheoremVerdict.Proven)
    assertEquals(e.verdict("unsat"),
      TheoremVerdict.Failed(List(Diagnostic(file, 10, true, "Tactic failure:\nno proof."))))
    assertEquals(e.verdict("impl"), TheoremVerdict.Missing)
    assertEquals((e.axiomsOf("made_book"), e.axiomsOf("unsat")), (Some(List("classic")), None))
    assertEquals(Elaboration(source, "", file, namespace).verdict("made_book"), TheoremVerdict.Missing)
    val broken = Elaboration(source, RocqReport.print(List(said.copy(broken = Some("Syntax error.")))), file, namespace)
    assertEquals(broken.verdict("made_book"), TheoremVerdict.Failed(List(Diagnostic(file, 0, true, "Syntax error."))))
  }

  test("a lemma states its obligation by the node's name; an authored proof's audit is read by its own name") {
    val e = Elaboration(source, RocqReport.print(List(RocqReport.File(file, Map.empty,
      Map("N_Proofs_complete" -> Nil), None))), file, List("Crm", "N", "Auto"))
    assertEquals((e.named("complete"), e.obligation("complete")), ("N_Auto_complete", "N_Obl_complete"))
    assertEquals(e.axiomsOf("complete"), Some(Nil))
  }

  test("every obligation's name reads back as the obligation") {
    val n = NodeId("Grants")
    val all = List(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.RootImpl,
      ObligationName.Made("in_room"), ObligationName.Consistent(0), ObligationName.Inhabited(n),
      ObligationName.Satisfiable(n, 0), ObligationName.Example("GrantedExamples", 3),
      ObligationName.ExampleOpposite("GrantedExamples", 3)) ++ (List(TryKind.Needed(n),
      TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle, TryKind.RestatesConjunct(n, 2))
      .map(ObligationName.Tried(_)))
    all.foreach(o => assertEquals(ObligationNames.read(LowerObligation.name(o).text), Some(o)))
    assertEquals(ObligationNames.read("helper"), None)
  }

  test("a proof file's lemmas, by the obligations they prove: those named for the node's proofs") {
    val proofs = "Lemma N_Proofs_made_book : N_Obl_made_book.\nProof.\n  auto.\nQed.\n\n" +
      "Lemma helper : True.\nProof.\n  auto.\nQed.\n\nLemma N_Proofs_impl : N_Obl_impl.\nProof.\n  auto.\nQed.\n"
    assertEquals(ProofRules.theorems(ProofFile(NodeId("N"), proofs)),
      List(ObligationName.Made("book"), ObligationName.Impl))
  }
