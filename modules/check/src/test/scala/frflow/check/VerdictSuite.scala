package frflow
package check

import frflow.fixtures.*
import frflow.lean.*
import frflow.protocol.{NodeKind as _, *}

/** The judges of a check, on Lean's output as Lean prints it (recorded), without running Lean. */
class VerdictSuite extends munit.FunSuite:
  import ObligationName.Probe

  private def elaborated(run: Run, src: String, rel: String) = Elaborated(run, Elaboration(src, run.output, rel))

  test("an obligation is judged by its theorem: its statement, what Lean said in it, whether Lean ran") {
    val proof = "theorem complete : Obl.complete := by\n  sorry\n\ntheorem weak : True := trivial\n"
    def judge(output: String, exit: Int = 0, authored: Boolean = false) =
      Verdict.judge(ObligationName.Complete, elaborated(Run.Done(exit, output), proof, "Proofs/T/N.lean"), authored)
    assertEquals(judge("Proofs/T/N.lean:1:8: warning: declaration uses `sorry`"), Result("complete", ObligationStatus.Open, "uses sorry"))
    assertEquals(judge("Proofs/T/N.lean:2:2: error: unsolved goals\n⊢ False", 1).detail, "unsolved goals\n⊢ False")
    assertEquals(judge("", 1), Result("complete", ObligationStatus.Open, "not checked: "))
    assertEquals(judge("", authored = true).status, ObligationStatus.Proven)
    assertEquals(Verdict.judge(ObligationName.Impl, elaborated(Run.Done(0, ""), proof.replace("weak", "impl"), "p"), true).status, ObligationStatus.Failed)
    assertEquals(Verdict.judge(ObligationName.Check, elaborated(Run.Done(0, ""), proof, "p"), true).detail, "no theorem check in p")
    // an authored proof uses only what a proof file may
    val cheat = "axiom cheat : False\ntheorem complete : Obl.complete := cheat.elim\n"
    assert(Verdict.judge(ObligationName.Complete, elaborated(Run.Done(0, ""), cheat, "p"), true).detail.startsWith("not allowed in a proof file"))
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
    def eval(name: ObligationName) = Eval(name, s"example $name", s"claim $name", s"not $name")
    val file = (List("eval_0", "eval_0_opposite", "eval_1", "eval_1_opposite", "eval_2", "eval_2_opposite", "probe_0", "probe_0_opposite")
      .map(t => s"theorem $t : True := by\n  frflow_eval\n")).mkString("\n")
    val evalRel = "FrFlowGen/T/N/Eval.lean"
    def at(theorem: Int) = s"$evalRel:${theorem * 3 + 2}:2: error: `grind` failed"
    // eval_0 proven, its opposite not; eval_1's opposite proven; eval_2 neither; the probe neither
    val output = List(at(1), at(2), at(4), at(5), at(6), at(7)).mkString("\n")
    val rs = Verdict.evaluations(List(ObligationName.Eval(0), ObligationName.Eval(1), ObligationName.Eval(2), Probe(0)).map(eval), List(ObligationName.Eval(3) -> "its parameters are functions"),
      Some(elaborated(Run.Done(1, output), file, evalRel)))
    assertEquals(rs.map(r => r.name -> r.status), List("eval_0" -> ObligationStatus.Proven, "eval_1" -> ObligationStatus.Failed,
      "eval_2" -> ObligationStatus.Unevaluated, "eval_3" -> ObligationStatus.Unevaluated))
    assertEquals(rs.head.detail, "Lean agrees: claim eval_0")
    assertEquals(rs(1).detail, "example eval_1: Scala computes claim eval_1, Lean proves not eval_1")
    val disagree = Verdict.agree(pick, rs)
    assertEquals(disagree.map(_.status), Some(CheckStatus.Failed))
    assert(disagree.exists(_.messages.head.startsWith("Lean and Scala disagree on 1 example(s)")), disagree)
    // Lean did not run at all: nothing is evaluated
    val none = Verdict.evaluations(List(eval(ObligationName.Eval(0))), Nil, Some(elaborated(Run.Done(1, "lake: no such file"), file, evalRel)))
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
    val rel = g.layout.checks(n.id).path
    val text = a.generated(rel)
    val tries = g.tries(n).map(_.obligation.name.lean).toSet
    val failing = LeanSource.theorems(text).filter(d => tries(d.name)).map(d => s"$rel:${d.from + 1}:2: error: frflow_auto found no proof")
    val audits = (List("holds") ++ g.extraObligations(n).map(_.name.lean)).map(t => s"'Shelf.${n.id}.Checks.$t' $axioms")
    elaborated(Run.Done(1, (failing ++ audits).mkString("\n")), text, rel)

  test("the verdict from the Checks file: the tries in plain words, the axioms audited, fail closed") {
    val a = Desk(shelfKb).analysis
    val root = Some(elaborated(Run.Done(0, "'Shelf.RootImpl.root_impl' does not depend on any axioms"), "theorem root_impl : Obl.root_impl := by\n  auto\n", "r"))
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
