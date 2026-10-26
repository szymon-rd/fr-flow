package frflow
package check

import frflow.fixtures.*
import frflow.lean.*
import frflow.protocol.*

/** What a check runs, in what order, and how it judges Lean's output (recorded as Lean prints it), without running Lean. */
class CheckSuite extends munit.FunSuite:
  import ObligationName.Probe

  private def elaborated(run: Run, src: String, rel: String) = Elaborated(run, Elaboration(src, run.output, rel))
  private val a = Desk(shelfKb).analysis
  private def ids(ns: List[Node[?]]) = ns.map(_.id)
  private def proven(n: Node[?]) = NodeId(n.id) -> NodeCheck(a.checkHash(n), CheckStatus.Proven, Nil, Nil, Nil, java.time.Instant.EPOCH)

  test("a node is checked after its parts, the nodes of one level side by side") {
    val plan = CheckPlan(a, None)
    assertEquals(ids(plan.todo), List("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    assertEquals(plan.levels.map(ids), List(List("Pick"), List("FromList", "OnlyLong", "EveryLong"), List("OnlyGood")))
    // the models first, in one build
    assertEquals(plan.prebuild, ids(plan.todo).map(id => s"FrFlowGen.Shelf.$id.Spec"))
    assertEquals(plan.theorems(List(pick)), List("FrFlowGen.Shelf.Pick.Theorems"))
  }

  test("a node whose check is current keeps it while its parts are proven; one node is checked whatever its record") {
    val recorded = a.withChecks(Map(proven(pick), proven(fromList)))
    val plan = CheckPlan(recorded, None)
    assertEquals(ids(plan.pending), List("OnlyGood", "OnlyLong", "EveryLong"))
    assertEquals(plan.theorems(List(fromList, onlyLong)), List("FrFlowGen.Shelf.OnlyLong.Theorems"))
    assertEquals(plan.kept(pick, plan.parts(pick, Map.empty)).map(_.status), Some(CheckStatus.Proven))
    // FromList is kept only once Pick, its part, is proven in this run or the record
    assertEquals(plan.parts(fromList, Map.empty), List("Pick" -> Some(CheckStatus.Proven)))
    val failed = Map("Pick" -> NodeCheck(Hash("h"), CheckStatus.Failed, Nil, Nil, Nil, java.time.Instant.EPOCH))
    assertEquals(plan.kept(fromList, plan.parts(fromList, failed)), None)
    // a recorded check of another hash is not current
    val stale = a.withChecks(Map(NodeId("Pick") -> NodeCheck(Hash("old"), CheckStatus.Proven, Nil, Nil, Nil, java.time.Instant.EPOCH)))
    assertEquals(CheckPlan(stale, None).pending.map(_.id).contains("Pick"), true)
    // checking one node: that node, checked again
    val one = CheckPlan(recorded, Some("Pick"))
    assertEquals((ids(one.todo), ids(one.pending)), (List("Pick"), List("Pick")))
  }

  test("check hashes depend on the Lean, not the words: a reworded statement keeps them") {
    def team(statement: String) =
      val top = Node.claim("Top", statement, why = "w")(forall((x: Term[BigInt]) => sq(x) >= 0))
      Desk(KnowledgeBase("Team", idea = "IDEA.md")(top, Node.claim("Floor", "Results are at least zero.", why = "w")(forall((x: Term[BigInt]) => sq(x) >= 0)).under(top))).analysis
    val (before, after) = (team("Results are never negative."), team("Results are never below zero."))
    def both(f: Analysis => Node[?] => Any, id: String) = (f(before)(before.kb.node(id).getOrElse(fail(id))), f(after)(after.kb.node(id).getOrElse(fail(id))))
    val (h1, h2) = both(_.checkHash, "Top")
    assertEquals(h1, h2)
    val (c1, c2) = both(_.hash, "Top")
    assertNotEquals(c1, c2)
    // the root's depends on everything root_impl composes
    assertNotEquals(a.checkHash(onlyGood), Desk(shelfKb.implementProven(pick)(longOnes)).analysis.checkHash(onlyGood))
  }

  test("an obligation is judged by its theorem: its statement, what Lean said in it, whether Lean ran") {
    val proof = "theorem complete : Obl.complete := by\n  sorry\n\ntheorem weak : True := trivial\n"
    def judge(output: String, exit: Int = 0, authored: Boolean = false) =
      Verdict.judge(ObligationName.Complete, elaborated(Run.Done(exit, output), proof, "Proofs/T/N.lean"), authored)
    assertEquals(judge("Proofs/T/N.lean:1:8: warning: declaration uses `sorry`"), Result(ObligationName.Complete, ObligationStatus.Open, "uses sorry"))
    assertEquals(judge("Proofs/T/N.lean:2:2: error: unsolved goals\n⊢ False", 1).detail, "unsolved goals\n⊢ False")
    assertEquals(judge("", 1), Result(ObligationName.Complete, ObligationStatus.Open, "not checked: "))
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
    def eval(name: ObligationName) = Eval(name, s"example $name", s"claim $name", s"not $name")
    val file = (List("eval_0", "eval_0_opposite", "eval_1", "eval_1_opposite", "eval_2", "eval_2_opposite", "probe_0", "probe_0_opposite")
      .map(t => s"theorem $t : True := by\n  frflow_eval\n")).mkString("\n")
    val evalRel = "FrFlowGen/T/N/Eval.lean"
    def at(theorem: Int) = s"$evalRel:${theorem * 3 + 2}:2: error: `grind` failed"
    // eval_0 proven, its opposite not; eval_1's opposite proven; eval_2 neither; the probe neither
    val output = List(at(1), at(2), at(4), at(5), at(6), at(7)).mkString("\n")
    val rs = Verdict.evaluations(List(ObligationName.Eval(0), ObligationName.Eval(1), ObligationName.Eval(2), Probe(0)).map(eval), List(ObligationName.Eval(3) -> "its parameters are functions"),
      Some(elaborated(Run.Done(1, output), file, evalRel)))
    assertEquals(rs.map(r => r.name.lean -> r.status), List("eval_0" -> ObligationStatus.Proven, "eval_1" -> ObligationStatus.Failed,
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

  test("an implementation proof: its statement, its build, the axioms it rests on") {
    val g = Generate(shelfKb)
    assertEquals(Verdict.implRules("theorem impl : Obl.impl := by\n  sorry\n"), None)
    assertEquals(Verdict.implRules("theorem impl : True := trivial\n").map(_.detail), Some("must state exactly Obl.impl"))
    val built = Run.Done(0, "'Shelf.Pick.Impl.impl' depends on axioms: [propext,\n Classical.choice]")
    assertEquals(Verdict.impl(g, pick, true, built, None), (Result(ObligationName.Impl, ObligationStatus.Proven, "authored"), Some(List("propext", "Classical.choice"))))
    assertEquals(Verdict.impl(g, pick, true, Run.Done(0, "'Shelf.Pick.Impl.impl' depends on axioms: [sorryAx]"), None)._1.detail, "uses sorry")
    assert(Verdict.impl(g, pick, false, Run.Done(1, ""), None)._1.detail.startsWith("not proven (auto): prove theorem impl"))
  }

  test("a node is proven with its parts: it waits for them; an open split asks for a proof") {
    val g = Generate(shelfKb)
    val proven = List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto"))
    assertEquals(Verdict.obligations(g, onlyGood, proven, proven, List("FromList" -> Some(CheckStatus.Proven))), None)
    assertEquals(Verdict.obligations(g, onlyGood, proven, proven, List("FromList" -> None)).map(j => (j.status, j.messages)),
      Some((CheckStatus.Waiting, List("waiting for its parts: FromList"))))
    val open = List(Result(ObligationName.Complete, ObligationStatus.Open, "x"))
    assertEquals(Verdict.obligations(g, onlyGood, open, open, Nil).flatMap(_.hint),
      Some("prove it in lean/Proofs/Shelf/OnlyGood.lean (run `scaffold OnlyGood`)"))
    // with a proof file, the proof in it is what to fix: no scaffold
    assertEquals(Verdict.obligations(g, onlyGood, open, open, Nil, proofFile = true).flatMap(_.hint),
      Some("fix the proof in lean/Proofs/Shelf/OnlyGood.lean"))
  }

  test("an authored proof that does not go through says so in FrFlow's words first, naming what changed, then Lean's") {
    val lean = Result(ObligationName.Complete, ObligationStatus.Open, "omega could not prove the goal")
    assertEquals(Verdict.brokenProof(lean, List("overlaps")).detail,
      "the proof from its parts no longer goes through: overlaps changed\nLean: omega could not prove the goal")
    assertEquals(Verdict.brokenProof(lean, Nil).detail,
      "the proof from its parts does not go through\nLean: omega could not prove the goal")
  }

  test("a broken proof whose Lean gives a counterexample says the step may be false, and to check the change first") {
    val omega = "omega could not prove the goal:\na possible counterexample may satisfy the constraints\n  c - d ≤ -1"
    val open = Result(ObligationName.Complete, ObligationStatus.Open, omega)
    val said = Verdict.brokenProof(open, List("overlaps"))
    assertEquals(said.detail, s"the step from its parts may no longer hold: overlaps changed\nLean: $omega")
    assertEquals(Verdict.brokenProof(open, Nil).detail.linesIterator.next(), "the step from its parts may not hold")
    assert(Verdict.mayBeFalse("decide failed: the proposition evaluates to false"))
    assert(!Verdict.mayBeFalse("omega could not prove the goal: no usable constraints found"))
    val g = Generate(shelfKb)
    assertEquals(Verdict.obligations(g, onlyGood, List(said), List(said), Nil, proofFile = true, changed = List("overlaps")).flatMap(_.hint),
      Some("check the change to overlaps; if the step still holds, fix the proof in lean/Proofs/Shelf/OnlyGood.lean"))
    // no counterexample: the proof is what to fix
    val plain = Verdict.brokenProof(Result(ObligationName.Complete, ObligationStatus.Open, "unsolved goals"), List("overlaps"))
    assertEquals(Verdict.obligations(g, onlyGood, List(plain), List(plain), Nil, proofFile = true, changed = List("overlaps")).flatMap(_.hint),
      Some("fix the proof in lean/Proofs/Shelf/OnlyGood.lean"))
  }

  test("what changed since a node was decided, as its proof reads it: the definitions it uses by name, its own formula") {
    import io.circe.Json
    def node(formula: String, uses: String*) = Content("sources" -> Json.obj("formula" -> Json.fromString(formula)),
      "why" -> Json.fromString("w"), "uses" -> Json.fromValues(uses.map(Json.fromString)))
    val before = node("f", "case class Booking(room: String)", "overlaps = (a, b) => a.start < b.end", "covers = (b, t) => b.start <= t")
    assertEquals(Verdict.whatChanged("Root", before, node("f", "case class Booking(room: String)", "overlaps = (a, b) => a.start <= b.end",
      "covers = (b, t) => b.start <= t")), List("overlaps"))
    assertEquals(Verdict.whatChanged("Root", before, node("g", "case class Booking(room: String, start: BigInt)",
      "overlaps = (a, b) => a.start < b.end", "covers = (b, t) => b.start <= t")), List("Root", "Booking"))
    assertEquals(Verdict.whatChanged("Root", before, before), Nil)
  }

  /** The node's Checks file as generated, and an output where Lean proves `holds` and the obligations, and none of the tries. */
  private def checked(a: Analysis, n: Node[?], axioms: String): Elaborated =
    val g = a.generate
    val rel = g.layout.checks(n.id).path
    val text = a.files.getOrElse(rel, "")
    val tries = g.tries(n).map(_.obligation.name.lean).toSet
    val failing = LeanSource.theorems(text).filter(d => tries(d.name)).map(d => s"$rel:${d.from + 1}:2: error: frflow_auto found no proof")
    val audits = (List("holds") ++ g.extraObligations(n).map(_.name.lean)).map(t => s"'Shelf.${n.id}.Checks.$t' $axioms")
    elaborated(Run.Done(1, (failing ++ audits).mkString("\n")), text, rel)

  test("the verdict from the Checks file: the tries in plain words, the axioms audited, fail closed") {
    val root = Some(Right(elaborated(Run.Done(0, "'Shelf.RootImpl.root_impl' does not depend on any axioms"), "theorem root_impl : Obl.root_impl := by\n  auto\n", "r")))
    val results = List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto"))
    val j = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "depends on axioms: [propext]"), root)
    assertEquals(j.status, CheckStatus.Proven, j)
    assertEquals(j.axioms, List("propext"))
    assertEquals(j.results.find(_.name.lean == "needed_FromList").map(r => (r.status, r.detail)),
      Some((ObligationStatus.NotShown, "Lean found no proof that OnlyGood holds without it (a try)")))
    assertEquals(j.results.find(_.name.lean == "clash").map(_.status), Some(ObligationStatus.NotShown))
    assertEquals(j.results.find(_.name.lean == "root_impl").map(_.detail), Some("the root holds of the code, trusting nothing; and the code of Pick, tested, not proven"))
    // an axiom outside what Lean's logic needs, or no audit at all: nothing is proven
    val unsound = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "depends on axioms: [cheat]"), root)
    assertEquals((unsound.status, unsound.messages), (CheckStatus.Failed, List("disallowed axioms: cheat")))
    val unaudited = Verdict.finish(a, onlyGood, results, None, checked(a, onlyGood, "was not printed"), root)
    assertEquals(unaudited.status, CheckStatus.Failed)
    assert(unaudited.messages.head.startsWith("Lean did not finish checking lean/FrFlowGen/Shelf/OnlyGood/Checks.lean"), unaudited.messages)
  }

  test("a RootImpl that does not build proves nothing of the code: the root is not proven, its own errors say why") {
    val results = List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto"))
    val source = "import FrFlowGen.Shelf.Pick.Impl\n\ntheorem root_impl : Obl.root_impl := by\n  auto\n"
    val checks = checked(a, onlyGood, "depends on axioms: [propext]")
    def judged(run: Run) = Verdict.finish(a, onlyGood, results, None, checks, Some(Right(elaborated(run, source, "FrFlowGen/Shelf/RootImpl.lean"))))
    def rootImpl(run: Run) = judged(run).results.find(_.name == ObligationName.RootImpl).map(r => (r.status, r.detail))
    // the import did not build: Lean says so before the theorem, and the message names the module, not where Lake keeps it
    val noImport = Run.Done(1, "FrFlowGen/Shelf/RootImpl.lean:1:0: error: object file '/w/lean/.lake/build/lib/lean/FrFlowGen/Shelf/Pick/Impl.olean' " +
      "of module FrFlowGen.Shelf.Pick.Impl does not exist")
    assertEquals(rootImpl(noImport),
      Some((ObligationStatus.Open, "the root is not proven of the code: FrFlowGen.Shelf.Pick.Impl did not build")))
    // what is not proven is in the results; the Checks file is not blamed
    assertEquals(judged(noImport).messages, Nil)
    // Lean stopped, saying nothing of the file; or it printed no axioms: it did not finish
    assertEquals(rootImpl(Run.Done(1, "error: build failed")).map(_._2),
      Some("the root is not proven of the code: not checked: error: build failed"))
    assert(rootImpl(Run.Done(0, "")).exists((s, d) => s == ObligationStatus.Open && d.contains("Lean did not print its axioms")))
  }

  test("root_impl is elaborated only once the proofs of the code it composes are built: one that does not build is the reason, by name") {
    val withCode = Desk(shelfKb.implementProven(pick)(longOnes)).analysis
    val g = withCode.generate
    val composed = Verdict.composed(withCode.kb, g, withCode.files.getOrElse(g.layout.rootImpl.path, ""))
    assertEquals(ids(composed), List("Pick"))
    assertEquals(Verdict.composedBuilt(g, composed, Run.Done(0, "Build completed successfully")), None)
    // as Lake prints a target that failed
    val failed = Run.Done(1, "✖ [28/28] Building FrFlowGen.Shelf.Pick.Impl (750ms)\n" +
      "error: FrFlowGen/Shelf/Pick/Impl.lean:16:8: Unknown identifier `bogus`\nSome required targets logged failures:\n- FrFlowGen.Shelf.Pick.Impl\nerror: build failed")
    val why = Verdict.composedBuilt(g, composed, failed)
    assertEquals(why, Some("Pick's impl did not build (check Pick says why)"))
    val judged = Verdict.finish(withCode, onlyGood, List(Result(ObligationName.Complete, ObligationStatus.Proven, "auto")), None,
      checked(withCode, onlyGood, "depends on axioms: [propext]"), why.map(Left(_)))
    assertEquals(judged.results.find(_.name == ObligationName.RootImpl).map(r => (r.status, r.detail)),
      Some((ObligationStatus.Open, "the root is not proven of the code: Pick's impl did not build (check Pick says why)")))
    assertEquals(Verdict.composedBuilt(g, composed, Run.TimedOut("")).map(_.contains("timed out")), Some(true))
  }

  test("the goal the first steps of a proof leave, as the stub and the message show it") {
    val goal = Run.Done(1, "/tmp/frflow-state1.lean:14:2: error: unsolved goals\nx : Int\n⊢ 0 ≤ x * x")
    assertEquals(ProofState.goal(goal, "frflow-state1.lean"), Some("x : Int\n⊢ 0 ≤ x * x"))
    assertEquals(ProofState.goal(Run.Done(0, ""), "frflow-state1.lean"), Some("no goals: these steps prove it"))
    assertEquals(ProofState.goal(Run.Done(1, "/tmp/frflow-state1.lean:3:0: error: unknown module"), "frflow-state1.lean"), None)
  }

