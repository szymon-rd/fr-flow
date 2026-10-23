package frflow
package check

import frflow.fixtures.*
import frflow.lean.*
import frflow.protocol.{NodeKind as _, *}

/** The judges of a check, on Lean's output as Lean prints it (recorded), without running Lean. */
class VerdictSuite extends munit.FunSuite:

  private val rel = "FrFlowGen/T/N/Checks.lean"
  private val src =
    """theorem a : 1 = 1 := by
      |  sorry
      |
      |theorem b : 1 = 2 := by
      |  decide
      |
      |theorem c : 2 = 2 := rfl
      |
      |#print axioms a
      |#print axioms c
      |""".stripMargin
  // What `lake env lean` printed of it (exit 1).
  private val out =
    s"""$rel:1:8: warning: declaration uses `sorry`
       |$rel:5:2: error: Tactic `decide` proved that the proposition
       |  1 = 2
       |is false
       |'a' depends on axioms: [sorryAx]
       |'c' does not depend on any axioms""".stripMargin
  private val ran = Elaborated(Run.Done(1, out), src, rel)

  test("a theorem holds when Lean reports no error in it, no sorry, and its axioms") {
    assertEquals(ran.why("a"), Some("uses sorry"))
    assert(ran.why("b").exists(_.startsWith("Tactic `decide` proved that the proposition\n  1 = 2\nis false")), ran.why("b"))
    assertEquals(ran.why("c"), None)
    assertEquals(ran.why("d"), Some("no theorem d"))
    assertEquals((ran.axiomsOf("a"), ran.axiomsOf("c"), ran.axiomsOf("b")), (Some(List("sorryAx")), Some(Nil), None))
    // the messages of another file are not this one's
    assertEquals(Elaborated(Run.Done(1, out.replace(rel, "Other.lean")), src, rel).why("b"), None)
  }

  test("an obligation is judged by its theorem: its statement, what Lean said in it, whether Lean ran") {
    val proof = "theorem complete : Obl.complete := by\n  sorry\n\ntheorem weak : True := trivial\n"
    def judge(output: String, exit: Int = 0, authored: Boolean = false) =
      Verdict.judge("complete", Elaborated(Run.Done(exit, output), proof, "Proofs/T/N.lean"), authored)
    assertEquals(judge("Proofs/T/N.lean:1:8: warning: declaration uses `sorry`"), Result("complete", ObligationStatus.Open, "uses sorry"))
    assertEquals(judge("Proofs/T/N.lean:2:2: error: unsolved goals\n⊢ False", 1).detail, "unsolved goals\n⊢ False")
    assertEquals(judge("", 1), Result("complete", ObligationStatus.Open, "not checked: "))
    assertEquals(judge("", authored = true).status, ObligationStatus.Proven)
    assertEquals(Verdict.judge("weak", Elaborated(Run.Done(0, ""), proof, "p"), true).status, ObligationStatus.Failed)
    assertEquals(Verdict.judge("other", Elaborated(Run.Done(0, ""), proof, "p"), true).detail, "no theorem other in p")
    // an authored proof uses only what a proof file may
    val cheat = "axiom cheat : False\ntheorem complete : Obl.complete := cheat.elim\n"
    assert(Verdict.judge("complete", Elaborated(Run.Done(0, ""), cheat, "p"), true).detail.startsWith("not allowed in a proof file"))
  }

  test("a model that does not build fails the node; one Lean took too long on is checked again") {
    assertEquals(Verdict.model(Run.Done(0, "")), None)
    assertEquals(Verdict.model(Run.TimedOut("")).map(_.status), Some(CheckStatus.Timeout))
    val broken = Verdict.model(Run.Done(1, "error: FrFlowGen/T/N/Spec.lean:3:4: unknown identifier 'x'"))
    assertEquals(broken.map(j => (j.status, j.messages)), Some((CheckStatus.ModelError, List("FrFlowGen/T/N/Spec.lean:3: unknown identifier 'x'"))))
    // with no diagnostic, the last lines of what Lean printed
    assertEquals(Verdict.errors(Run.Done(1, "a\nb\nc")), List("a\nb\nc"))
  }

  test("the examples are evaluated: Lean agrees, disagrees, decides neither, or did not run") {
    val g = Generate(shelfKb)
    def eval(name: String) = g.Eval(name, s"example $name", s"claim $name", s"not $name")
    val file = (List("eval_0", "eval_0_opposite", "eval_1", "eval_1_opposite", "eval_2", "eval_2_opposite", "probe_0", "probe_0_opposite")
      .map(t => s"theorem $t : True := by\n  frflow_eval\n")).mkString("\n")
    val evalRel = "FrFlowGen/T/N/Eval.lean"
    def at(theorem: Int) = s"$evalRel:${theorem * 3 + 2}:2: error: `grind` failed"
    // eval_0 proven, its opposite not; eval_1's opposite proven; eval_2 neither; the probe neither
    val output = List(at(1), at(2), at(4), at(5), at(6), at(7)).mkString("\n")
    val rs = Verdict.evaluations(List("eval_0", "eval_1", "eval_2", "probe_0").map(eval), List("eval_3" -> "its parameters are functions"),
      Some(Elaborated(Run.Done(1, output), file, evalRel)))
    assertEquals(rs.map(r => r.name -> r.status), List("eval_0" -> ObligationStatus.Proven, "eval_1" -> ObligationStatus.Failed,
      "eval_2" -> ObligationStatus.Unevaluated, "eval_3" -> ObligationStatus.Unevaluated))
    assertEquals(rs.head.detail, "Lean agrees: claim eval_0")
    assertEquals(rs(1).detail, "example eval_1: Scala computes claim eval_1, Lean proves not eval_1")
    val disagree = Verdict.agree(pick, rs)
    assertEquals(disagree.map(_.status), Some(CheckStatus.Failed))
    assert(disagree.exists(_.messages.head.startsWith("Lean and Scala disagree on 1 example(s)")), disagree)
    // Lean did not run at all: nothing is evaluated
    val none = Verdict.evaluations(List(eval("eval_0")), Nil, Some(Elaborated(Run.Done(1, "lake: no such file"), file, evalRel)))
    assert(none.head.detail.startsWith("example eval_0: Lean did not run: lake: no such file"), none)
    assertEquals(Verdict.agree(pick, none), None)
  }

  test("lemmas shared by proofs: imported only as the lemma module, filtered like a proof, built without sorry") {
    val g = Generate(squareKb)
    val importing = "import Proofs.Square.Lemmas\ntheorem complete : Obl.complete := by\n  sorry\n"
    assertEquals(Verdict.lemmas(g, "theorem complete : Obl.complete := by\n  sorry\n", None), Right(false))
    assert(Verdict.lemmas(g, importing.replace("Square", "Other"), None).left.exists(_.messages.head.contains("may import only Proofs.Square.Lemmas")))
    assert(Verdict.lemmas(g, importing, None).left.exists(_.messages.head.contains("does not exist")))
    assert(Verdict.lemmas(g, importing, Some("axiom sq : False\n")).left.exists(_.messages.head.startsWith("not allowed in lean/Proofs/Square/Lemmas.lean")))
    assertEquals(Verdict.lemmas(g, importing, Some("theorem sq : True := trivial\n")), Right(true))
    assertEquals(Verdict.lemmasBuilt(g, Run.Done(0, "warning: declaration uses 'sorry'")).map(_.messages), Some(List("lean/Proofs/Square/Lemmas.lean uses sorry")))
    assertEquals(Verdict.lemmasBuilt(g, Run.Done(0, "")), None)
  }

  test("an authored implementation proof: its statement, its build, the axioms it rests on") {
    assertEquals(Verdict.implRules("theorem impl : Obl.impl := by\n  sorry\n"), None)
    assertEquals(Verdict.implRules("theorem impl : True := trivial\n").map(_.detail), Some("must state exactly Obl.impl"))
    val built = Run.Done(0, "'Shelf.Pick.Impl.impl' depends on axioms: [propext,\n Classical.choice]")
    assertEquals(Verdict.implAxioms(built), List("propext", "Classical.choice"))
    assertEquals(Verdict.implAuthored(built), Result("impl", ObligationStatus.Proven, "authored"))
    assertEquals(Verdict.implAuthored(Run.Done(0, "'Shelf.Pick.Impl.impl' depends on axioms: [sorryAx]")).detail, "uses sorry")
    assertEquals(Verdict.implAxioms(Run.Done(1, "")), List(Verdict.NoAudit))
  }

  test("a node is proven with its parts: it waits for them; an open split asks for a proof") {
    val g = Generate(shelfKb)
    val proven = List(Result("complete", ObligationStatus.Proven, "auto"))
    assertEquals(Verdict.obligations(g, onlyGood, proven, proven, List("FromList" -> Some(CheckStatus.Proven))), None)
    assertEquals(Verdict.obligations(g, onlyGood, proven, proven, List("FromList" -> None)).map(j => (j.status, j.messages)),
      Some((CheckStatus.Waiting, List("waiting for its parts: FromList"))))
    val open = List(Result("complete", ObligationStatus.Open, "x"))
    assertEquals(Verdict.obligations(g, onlyGood, open, open, Nil).map(_.messages),
      Some(List("prove it in lean/Proofs/Shelf/OnlyGood.lean (run `scaffold OnlyGood`)")))
  }

  /** The node's Checks file as generated, and an output where Lean proves `holds` and the obligations, and none of the tries. */
  private def checked(a: Analysis, n: Node[?], axioms: String): Elaborated =
    val g = a.generate
    val rel = g.checksPath(n.id)
    val text = a.generated(rel)
    val tries = g.tries(n).map(_.obligation.name).toSet
    val failing = Lean.theorems(text).filter(d => tries(d.name)).map(d => s"$rel:${d.from + 1}:2: error: frflow_auto found no proof")
    val audits = (List("holds") ++ g.extraObligations(n).map(_.name)).map(t => s"'Shelf.${n.id}.Checks.$t' $axioms")
    Elaborated(Run.Done(1, (failing ++ audits).mkString("\n")), text, rel)

  test("the verdict from the Checks file: the tries in plain words, the axioms audited, fail closed") {
    val a = Desk(shelfKb).analysis
    val root = Some(Elaborated(Run.Done(0, "'Shelf.RootImpl.root_impl' does not depend on any axioms"), "theorem root_impl : Obl.root_impl := by\n  auto\n", "r"))
    val results = List(Result("complete", ObligationStatus.Proven, "auto"))
    val j = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "depends on axioms: [propext]"), root)
    assertEquals(j.status, CheckStatus.Proven, j)
    assertEquals(j.axioms, List("propext"))
    assertEquals(j.results.find(_.name == "needed_FromList").map(r => (r.status, r.detail)),
      Some((ObligationStatus.Needed, "Lean found no proof that OnlyGood holds without it (a try)")))
    assertEquals(j.results.find(_.name == "clash").map(_.status), Some(ObligationStatus.NoClash))
    assertEquals(j.results.find(_.name == "root_impl").map(_.detail), Some("the root holds of the code, trusting Pick"))
    // an axiom outside what Lean's logic needs, or no audit at all: nothing is proven
    val unsound = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "depends on axioms: [cheat]"), root)
    assertEquals((unsound.status, unsound.messages), (CheckStatus.Failed, List("disallowed axioms: cheat")))
    val unaudited = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "was not printed"), root)
    assertEquals(unaudited.status, CheckStatus.Failed)
    assert(unaudited.messages.head.startsWith("Lean did not finish checking lean/FrFlowGen/Shelf/OnlyGood/Checks.lean"), unaudited.messages)
  }

  test("the goal the first steps of a proof leave, as the stub and the message show it") {
    val goal = Run.Done(1, "/tmp/frflow-state1.lean:14:2: error: unsolved goals\nx : Int\n⊢ 0 ≤ x * x")
    assertEquals(ProofState.goal(goal, "frflow-state1.lean"), Some("x : Int\n⊢ 0 ≤ x * x"))
    assertEquals(ProofState.goal(Run.Done(0, ""), "frflow-state1.lean"), Some("no goals: these steps prove it"))
    assertEquals(ProofState.goal(Run.Done(1, "/tmp/frflow-state1.lean:3:0: error: unknown module"), "frflow-state1.lean"), None)
  }

  test("a check is stamped with the hash it was made against") {
    val j = Judged(CheckStatus.Open, Nil, List("m"))
    assertEquals(j.withEvaluations(List(Result("eval_0", ObligationStatus.Proven))).stamp(Hash("h"), java.time.Instant.EPOCH),
      NodeCheck(Hash("h"), CheckStatus.Open, List(Result("eval_0", ObligationStatus.Proven)), List("m"), Nil, "1970-01-01T00:00:00Z"))
  }
