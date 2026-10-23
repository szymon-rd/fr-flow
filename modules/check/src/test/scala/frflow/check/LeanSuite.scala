package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.lean.*
import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.{NodeKind as _, *}
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** End to end against Lean. Skipped when `lake` is not available. */
class LeanSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  private lazy val kernel: Path =
    Iterator.iterate(Paths.get(sys.props("user.dir")).toAbsolutePath)(_.getParent).takeWhile(_ != null)
      .map(_.resolve("lean")).find(p => Files.exists(p.resolve("FrFlow.lean"))).getOrElse(fail("kernel not found"))

  private def lake(dir: Path): Lake = Config.load.flatMap(Lake(dir, _)).unsafeRunSync()
  private def lakeAvailable: Boolean = lake(Paths.get(".")).available.unsafeRunSync()

  /** A workflow in a fresh workspace, its operations run one after another. */
  private final class Lab(w: Workflow):
    def ws: Workspace = w.ws
    def check(only: Option[String] = None): List[(Node[?], NodeCheck)] = w.check(only).unsafeRunSync().results
    def analysis: Analysis = w.analysis.unsafeRunSync()
    def generate: Generate = analysis.generate
    def baseSnapshot: Snapshot = analysis.snapshot
    def scaffold(n: Node[?]): Boolean = w.scaffold(n).unsafeRunSync().isDefined
    def status: String = Status.text(w.status.unsafeRunSync())

  private def workflow(kb: KnowledgeBase): Lab =
    assume(lakeAvailable, "lake is not available")
    Lab(Workflow(kb, Workspace(Files.createTempDirectory("frflow"), kernel.toString)).unsafeRunSync())

  private def statuses(r: List[(Node[?], NodeCheck)]) = r.map((n, c) => n.id -> c.status.toString)
  private def of(r: List[(Node[?], NodeCheck)], id: String) = r.find(_._1.id == id).get._2
  private def result(c: NodeCheck, name: String) = c.obligations.find(_.name == name)
  private def node(w: Lab, id: String) = w.baseSnapshot.nodes.find(_.id == NodeId(id)).get
  private def splitOf(w: Lab, n: Node[?]) = node(w, n.id).split.get
  private def st(split: Split, k: String) = Some((if k == "clash" then split.clash else split.complete).status.toString)

  test("the shelf is proven by automation: each node from its parts, the root from the leaves, of the code from what is trusted") {
    val w = workflow(shelfKb.implementProven(pick)(longOnes))
    val r = w.check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "FromList" -> "proven", "OnlyLong" -> "proven", "EveryLong" -> "proven", "Pick" -> "proven"))
    assert(r.flatMap(_._2.axioms).forall(Lean.allowedAxioms))
    // the root's parts make it only together: each is needed, and they do not clash
    val root = of(r, "OnlyGood")
    assertEquals(root.obligations.filter(o => o.name.startsWith("needed_") || Set("complete", "clash", "unsat")(o.name)).map(o => o.name -> o.status.toString),
      List("complete" -> "proven", "needed_FromList" -> "needed", "needed_OnlyLong" -> "needed", "needed_EveryLong" -> "needed", "clash" -> "no-clash", "unsat" -> "not-unsat"))
    assertEquals(result(root, "idle").map(_.status.toString), Some("not-idle"))
    // each said plainly in the snapshot's split too
    assertEquals(splitOf(w, onlyGood).needed.map(_.status), List.fill(3)(ObligationStatus.Needed))
    assertEquals(st(splitOf(w, onlyGood), "clash"), Some("no-clash"))
    // Pick has three parents: each is proven from it, and it is proven once
    assertEquals(List(fromList, onlyLong, everyLong).map(n => st(splitOf(w, n), "complete")), List.fill(3)(Some("proven")))
    assertEquals(result(of(r, "Pick"), "impl").map(_.status.toString), Some("proven"))
    // the code is proven: nothing is trusted
    assertEquals(result(root, "root_impl").map(r => (r.status.toString, r.detail)), Some(("proven", "the root holds of the code, trusting nothing")))
    assertEquals(w.generate.trusted, Nil)
    assert(w.status.contains("Trusted (the hypotheses of root_impl, proven): nothing."), w.status)
  }

  test("two modules proving things of one match with a wildcard can be imported together: its equations are made where it is defined") {
    assume(lakeAvailable, "lake is not available")
    val dir = Files.createTempDirectory("sparse")
    Files.writeString(dir.resolve("lakefile.toml"),
      s"name = \"sparse\"\n\n[[require]]\nname = \"frflow\"\npath = \"$kernel\"\n\n[[lean_lib]]\nname = \"Sparse\"\nglobs = [\"Sparse.+\"]\n")
    Files.writeString(dir.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
    def file(name: String, text: String) = { Files.createDirectories(dir.resolve("Sparse")); Files.writeString(dir.resolve(s"Sparse/$name.lean"), text) }
    // As the vocabulary module declares a `define` with a wildcard case, and two nodes' modules use `grind` on it.
    def base(eqns: Boolean) =
      "import FrFlow\ninductive Req where\n  | signIn (t : String)\n  | signOut (t : String)\n  | admin (on : Bool)\n" +
        "def tokenOf : Req → Option String\n  | .signIn t => some t\n  | _ => none\n" + (if eqns then "frflow_match_eqns\n" else "")
    def uses(b: String) = List(
      s"import Sparse.$b\ntheorem a (q : Req) (t : String) (h : tokenOf q = some t) : q = .signIn t := by\n  unfold tokenOf at h; grind\n",
      s"import Sparse.$b\ntheorem b (q : Req) (t : String) (h : tokenOf q = some t) : ∃ u, q = .signIn u := by\n  unfold tokenOf at h; grind\n")
    file("Base", base(true)); file("A", uses("Base")(0)); file("B", uses("Base")(1)); file("C", "import Sparse.A\nimport Sparse.B\n")
    val lk = lake(dir)
    val built = lk.build("Sparse.C").unsafeRunSync()
    assert(built.ok, built.output)
    // Without it, each module makes the equations, and Lean's auxiliary declaration twice (Lean 4.35).
    file("Base0", base(false)); file("A0", uses("Base0")(0)); file("B0", uses("Base0")(1)); file("C0", "import Sparse.A0\nimport Sparse.B0\n")
    val clash = lk.build("Sparse.C0").unsafeRunSync()
    assert(!clash.ok && clash.output.contains("already contains"), clash.output)
    // The generated modules that declare functions make their equations
    val g = Generate(shelfKb)
    assert(g.domain.contains("frflow_match_eqns") && g.spec(onlyGood).contains("frflow_match_eqns"), g.domain)
  }

  test("root_impl rests on what is trusted: an assumption on an operation the code calls, and a contract with plain code") {
    val kb = shelfWith(pick, shelfPort).implementProven(pick)(viaFetch).implementProven(shelfPort)(fromService, (shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    assertEquals(w.generate.trusted.map(_.id), List("ShelfPort"))
    val r = w.check()
    assert(r.forall(_._2.status.toString == "proven"), statuses(r))
    assertEquals(result(of(r, "OnlyGood"), "root_impl").map(_.status.toString), Some("proven"))
    // the assumption's check follows from its post, and the code beside its reference is checked against it
    val port = of(r, "ShelfPort")
    assertEquals(port.obligations.filter(o => Set("check", "impl")(o.name)).map(o => o.name -> o.status.toString).toSet, Set("check" -> "proven", "impl" -> "proven"))
    // Pick's code is proven from the assumption's promise alone
    assert(w.generate.obligation(pick, "impl").get.statement.contains("h_ShelfPort"), w.generate.obligation(pick, "impl"))
    assertEquals(w.baseSnapshot.trusted, List(NodeId("ShelfPort")))
    // service runs the check, not the post: a book off the shelf passes it, a short book does not
    val off = kb.implement(shelfPort)((shelf, n) => List(Book("Elsewhere", 500)))
    assertEquals(off.service(shelfPort)(minPages.bind(100))(Nil, 1), List(Book("Elsewhere", 500)))
    val short = kb.implement(shelfPort)((shelf, n) => List(Book("Short", 20)))
    intercept[ContractViolation](short.service(shelfPort)(minPages.bind(100))(Nil, 1))
    // with plain code, Pick itself is trusted
    assertEquals(Generate(shelfKb).trusted.map(_.id), List("Pick"))
  }

  test("parts that do not make their parent are not accepted") {
    val r = workflow(sloppyKb).check()
    assertEquals(statuses(r), List("OnlyGood" -> "open", "Sloppy" -> "proven"))
    // with the goal a proof by hand starts from: after the stub's first steps, the parts by their names
    assert(result(of(r, "OnlyGood"), "complete").exists(d => d.detail.contains("the goal is:") && d.detail.contains("h_Sloppy :") && d.detail.contains("⊢")),
      of(r, "OnlyGood").obligations)
  }

  test("a part the parent holds without is not needed: the split is unproven") {
    val bounded = Node.claim("Bounded", "No more books are picked than the shelf holds.", why = "w")(
      forall((l: List[Book], n: Int) => picks(l, n).length <= l.length)).under(onlyGood)
    val w = workflow(shelfWith(pick, bounded))
    val r = w.check()
    val root = of(r, "OnlyGood")
    assertEquals(result(root, "complete").map(_.status.toString), Some("proven"))
    assertEquals(result(root, "needed_Bounded").map(_.status.toString), Some("not-needed"), root.obligations)
    assertEquals(result(root, "needed_FromList").map(_.status.toString), Some("needed"), root.obligations)
    val needed = splitOf(w, onlyGood).needed.map(n => n.id.value -> n.status.toString).toMap
    assertEquals(needed("Bounded"), "not-needed")
    val n = node(w, "OnlyGood")
    assert(Reports.unproven(n).exists(_.startsWith("Bounded is not needed for it")), Reports.unproven(n))
  }

  test("parts that contradict each other fail their parent, however complete") {
    val none = Node.claim("NoneLong", "No book is ever picked.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).isEmpty)).under(onlyGood)
    val one = Node.claim("OneAlways", "One book is always picked.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).length == 1)).under(onlyGood)
    val w = workflow(KnowledgeBase("Clash", idea = "IDEA.md")(onlyGood, books, picking, none, one))
    val root = of(w.check(), "OnlyGood")
    assertEquals(root.status.toString, "failed", root)
    assertEquals(result(root, "clash").map(_.status.toString), Some("clash"))
    assertEquals(st(splitOf(w, onlyGood), "clash"), Some("clash"))
  }

  test("a root doing nothing meets is unproven: it must say what users can do") {
    val guard = Node.claim("Guard", "A picked item is on the list and good.", why = "w")(
      forall((l: List[Item.T], x: Item.T) => shown(l, x) ==> (l.contains(x) && good(x))))
    val c = Node.contract(picks)("GuardPick", "A call returns only long books from the shelf.", why = "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(guard)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300)), 5, List(Book("Long", 300)), "the long book"),
        expect(List(Book("Short", 20)), 5, Nil, "none"),
        reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
    val w = workflow(KnowledgeBase("Guard", idea = "IDEA.md")(guard, books, picking, c))
    val root = of(w.check(), "Guard")
    assertEquals(result(root, "idle").map(_.status.toString), Some("idle"), root)
    val n = node(w, "Guard")
    assert(Reports.unproven(n).exists(_.contains("doing nothing meets it")), Reports.unproven(n))
    // the shelf's root says exactly: doing nothing does not meet it
    assert(!workflow(shelfKb).check().exists((n, c) => result(c, "idle").exists(_.status.toString == "idle")))
  }

  private val feasible = "  unfold Obl.feasible\n  exact ⟨fun x => x * x, by simp [frflow_defs]⟩"
  /** A scaffolded stub (its first steps, the goal they leave, `sorry`) replaced by a proof. */
  private def fill(src: String, o: String, proof: String) =
    src.replaceFirst(s"(?s)  unfold Obl\\.$o\n.*?  sorry\n", java.util.regex.Matcher.quoteReplacement(proof + "\n"))

  test("an obligation automation cannot prove is proven in the node's proof file, with a witness") {
    val w = workflow(squareKb)
    val first = w.check()
    assertEquals(statuses(first), List("NonNegative" -> "open", "Squares" -> "proven"))
    // automation gave up: what to write, and where, first
    assert(result(of(first, "NonNegative"), "complete").exists(_.detail.startsWith(
      "automation gave up: write theorem complete : Obl.complete in lean/Proofs/Square/NonNegative.lean (run `scaffold NonNegative`)")), of(first, "NonNegative"))
    // the goal check prints is the one the stub's first steps leave, written in the stub too
    val gaveUp = result(of(first, "NonNegative"), "complete").get.detail
    assert(gaveUp.contains("After `unfold Obl.complete; frflow_intro; simp only [frflow_defs] at *`") && gaveUp.contains("h_Squares : ∀ (x : Int), sq x = x * x"), gaveUp)
    assert(w.scaffold(nonNegative))
    val file = w.ws.lean.resolve(w.generate.proofsPath("NonNegative"))
    val stub = Files.readString(file)
    assert(stub.contains("  unfold Obl.complete\n  frflow_intro\n  simp only [frflow_defs] at *\n  /- The goal here") &&
      stub.contains("h_Squares : ∀ (x : Int), sq x = x * x"), stub)
    assertEquals(result(w.check(Some("NonNegative")).head._2, "complete").map(_.detail), Some("uses sorry"))

    def edit(f: String => String) = Files.writeString(file, f(Files.readString(file)))
    // from the stub's first steps, the binders by their names
    Files.writeString(file, fill(stub, "complete",
      """  unfold Obl.complete
        |  frflow_intro
        |  simp only [frflow_defs] at *
        |  intro x
        |  rw [h_Squares x]
        |  rcases Int.le_total 0 x with hx | hx
        |  · exact Int.mul_nonneg hx hx
        |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
        |    simpa [Int.neg_mul_neg] using this""".stripMargin))
    // an authored proof needs a witness that something meets the parts
    val noWitness = w.check(Some("NonNegative")).head._2
    assertEquals(result(noWitness, "feasible").map(_.status.toString), Some("open"), noWitness)
    assertEquals(st(splitOf(w, nonNegative), "complete"), Some("open"))
    edit(fill(_, "feasible", feasible))
    val proven = w.check(Some("NonNegative")).head._2
    assertEquals(st(splitOf(w, nonNegative), "complete"), Some("proven"))
    assertEquals((proven.status.toString, result(proven, "complete").map(_.detail)), ("proven", Some("authored")), proven)
    assert(!Files.readString(w.ws.lean.resolve(w.generate.autoPath("NonNegative"))).contains("theorem complete"))
    // a proof of something weaker does not count
    edit(src => src.replaceAll("(?s)theorem complete : Obl.complete := by.*?(?=\ntheorem feasible)", "theorem complete : True := trivial\n"))
    assertEquals(result(w.check(Some("NonNegative")).head._2, "complete").map(_.status.toString), Some("failed"))
  }

  test("proofs may share lemmas, which are filtered and replayed like them") {
    val w = workflow(squareKb)
    w.check()
    assert(w.scaffold(nonNegative))
    val file = w.ws.lean.resolve(w.generate.proofsPath("NonNegative"))
    val lemmas = w.ws.lean.resolve(w.generate.lemmasPath)
    def lemma(body: String) = Files.writeString(lemmas,
      s"import FrFlow\n\nnamespace Square.Lemmas\n\n$body\n\nend Square.Lemmas\n")
    lemma("""theorem sq (x : Int) : 0 ≤ x * x := by
            |  rcases Int.le_total 0 x with hx | hx
            |  · exact Int.mul_nonneg hx hx
            |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
            |    simpa [Int.neg_mul_neg] using this""".stripMargin)
    val src = Files.readString(file)
    Files.writeString(file, fill(fill(src.replaceFirst("import ", "import Proofs.Square.Lemmas\nimport "),
      "complete", "  unfold Obl.complete\n  intro sq h\n  simp only [frflow_defs] at *\n  intro x\n  rw [h x]\n  exact Square.Lemmas.sq x"),
      "feasible", feasible))
    val proven = w.check(Some("NonNegative")).head._2
    assertEquals((proven.status.toString, result(proven, "complete").map(_.detail)), ("proven", Some("authored")), proven)
    // a lemma file gets the same filter as a proof file
    lemma("axiom sq (x : Int) : 0 ≤ x * x")
    val bad = w.check(Some("NonNegative")).head._2
    assertEquals(bad.status.toString, "failed", bad)
    assert(bad.messages.exists(_.contains("not allowed in lean/Proofs/Square/Lemmas.lean")), bad.messages)
  }

  test("a parent that holds whatever its one part says is vacuous; a node no world meets fails") {
    val trivial = Node.claim("Trivial", "Nothing is wrong.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).forall(b => true)))
    val part = Node.claim("Part", "Picked books come from the shelf.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(trivial)
    val r = workflow(KnowledgeBase("Vac", idea = "IDEA.md")(trivial, part)).check()
    assertEquals(result(of(r, "Trivial"), "vacuous").map(_.status.toString), Some("not-needed"), of(r, "Trivial"))
    // a node that says what its one part says: a warning
    val same = Node.claim("Same", "Picked books come from the shelf.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b))))
    val again = Node.claim("Again", "Every book picked is on the shelf.", why = "w")(forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(same)
    val sw = workflow(KnowledgeBase("Same", idea = "IDEA.md")(same, again))
    val sr = sw.check()
    assertEquals(result(of(sr, "Same"), "restates").map(_.status.toString), Some("restates"), of(sr, "Same"))
    assertEquals(result(of(r, "Trivial"), "restates").map(_.status.toString), Some("not-restates"), of(r, "Trivial"))
    assert(sw.status.contains("warning: Same says what Again says: merge them, or say what Same adds"), sw.status)
    val never = Node.claim("Never", "The service picks more books than it picks.", why = "w")(
      picks(List(Book("A", 1)), 1).length > picks(List(Book("A", 1)), 1).length).under(onlyGood)
    val u = of(workflow(KnowledgeBase("Unsat", idea = "IDEA.md")(onlyGood, books, picking, never)).check(), "Never")
    assertEquals(u.status.toString, "failed", u)
    assert(u.messages.exists(_.contains("no world meets it")), u.messages)
  }

  test("an invariant is a claim proven from the contracts that keep it, or left open") {
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).under(onlyGood)
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "w")((asked, picked) => picked <= asked).under(onlyGood)
    val inName = Node.invariant[List[Book], Book]("InName", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).under(onlyGood)
    val kept = pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b)))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
      // a view that shows the rule only what it accepts keeps nothing
      .keeps(inName)((shelf, n, picked) => picked.filter(b => shelf.contains(b)).map(b => (shelf, b)))
    val kb = shelfWith(kept, fromShelf, atMostN, inName).implement(kept)((shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val r = w.check()
    assertEquals(result(of(r, "FromShelf"), "complete").map(_.status.toString), Some("proven"), of(r, "FromShelf"))
    // the view lists every book picked, with the shelf it was asked of
    assertEquals(result(of(r, "Pick"), "cover_FromShelf").map(_.status.toString), Some("proven"), of(r, "Pick"))
    // a rule about numbers is not about what the result holds
    assertEquals(result(of(r, "Pick"), "cover_AtMostN"), None)
    assertEquals(result(of(r, "AtMostN"), "complete").map(_.status.toString), Some("open"))
    assertEquals(result(of(r, "InName"), "vacuous").map(_.status.toString), Some("not-needed"), of(r, "InName"))
    val inv = node(w, "Pick").invariants.map(i => i.id.value -> i.status.toString).toMap
    assertEquals(inv, Map("FromShelf" -> "proven", "AtMostN" -> "open", "InName" -> "open"))
  }

  test("a view that leaves out what the result holds keeps nothing, however it hides the condition") {
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).under(onlyGood)
    val hidden = pick.keeps(fromShelf)((shelf, n, picked) => onShelf(shelf, picked).map(b => (shelf, b)))
    val c = of(workflow(shelfWith(hidden, fromShelf)).check(), "Pick")
    assertEquals(result(c, "cover_FromShelf").map(_.status.toString), Some("open"), c)
  }

  test("Lean evaluates each example as Scala does, and a disagreement fails the node") {
    val c = of(workflow(shelfKb).check(), "Pick")
    assertEquals(c.obligations.filter(_.name.startsWith("eval")).map(o => o.name -> o.status.toString),
      List("eval_0" -> "proven", "eval_1" -> "proven", "eval_2" -> "proven", "eval_3" -> "proven"), c)
    // A parameter that is no fixed value: Lean is given one value of it, Scala's post reads another.
    var flip = false
    val unstable = Node.contract(picks)("Unstable", "Picking returns only long enough books.", why = "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(shelfParts*)
      .examples(minPages.bind { flip = !flip; if flip then 100 else 10 })(
        expect(List(Book("Mid", 50)), 5, List(Book("Mid", 50)), "a book of 50 pages"),
        reject(List(Book("Mid", 50)), 5, List(Book("Other", 50)), "not a book from the shelf"))
    val u = of(workflow(shelfWith(unstable)).check(), "Unstable")
    assertEquals(u.status.toString, "failed", u)
    assertEquals(result(u, "eval_0").map(_.status.toString), Some("failed"), u)
    assertEquals(result(u, "eval_1").map(_.status.toString), Some("proven"), u)
    assert(u.messages.head.contains("Lean and Scala disagree"), u.messages)
  }

  test("probes near the examples find a translation bug the examples miss") {
    def kb(d: Def[(List[BigInt], BigInt) => List[BigInt]]) = KnowledgeBase("Probe", idea = "IDEA.md")(floorRoot, floorKeep).implementProven(floorKeep)(d)
    val good = of(workflow(kb(keepAtLeast)).check(), "FloorKeep")
    assertEquals(good.status.toString, "proven", good)
    assert(good.obligations.count(o => o.name.startsWith("probe") && o.status.toString == "proven") >= 3, good.obligations)
    // A translation bug, injected: the Lean of the code says > where the Scala says >=. The examples
    // agree; a probe at the boundary does not.
    val l = keepAtLeast.lifted
    assert(l.body.contains("≥"), l.body)
    val wrong = Def(keepAtLeast.name, new Lifted(() => l.value, l.params, l.result, l.body.replace("≥", ">"), l.source, l.types, l.opaques,
      l.paramRefs, () => l.defs, () => l.paramObjects, () => l.opaqueObjects))
    val bad = of(workflow(kb(wrong)).check(), "FloorKeep")
    assertEquals(bad.status.toString, "failed", bad)
    assert(bad.obligations.filter(_.name.startsWith("eval")).forall(_.status.toString == "proven"), bad.obligations)
    assert(bad.obligations.exists(o => o.name.startsWith("probeImpl") && o.status.toString == "failed"), bad.obligations)
  }

  test("an implementation written as a define is proven to keep its contract, and its results are evaluated in Lean") {
    val kb = shelfKb.implementProven(pick)(longOnes)
    assert(kb.exampleResults(pick).forall(_.implementation.contains("ok")), kb.exampleResults(pick))
    val c = of(workflow(kb).check(), "Pick")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assertEquals(c.obligations.filter(_.name.startsWith("evalImpl")).map(_.status.toString), List.fill(4)("proven"), c)
    // one that can return a short book is not proven
    val w2 = workflow(shelfKb.implementProven(pick)(anyOnes))
    val bad = of(w2.check(), "Pick")
    assertEquals(result(bad, "impl").map(_.status.toString), Some("open"))
    // scaffold stubs what is open: the implementation
    assert(w2.scaffold(pick))
    val src = Files.readString(w2.ws.lean.resolve(w2.generate.proofsPath("Pick")))
    assert(src.contains("theorem impl : Obl.impl") && !src.contains("theorem complete"), src)
    val again = w2.check(Some("Pick")).head._2
    assertEquals(result(again, "impl").map(r => (r.status.toString, r.detail)), Some(("open", "uses sorry")), again)
  }

  test("code using flatMap is proven to meet its contract, and evaluated in Lean") {
    val c = of(workflow(shelfKb.implementProven(pick)(firstLong)).check(), "Pick")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(c.obligations.filter(_.name.startsWith("eval_")).forall(_.status.toString == "proven"), c)
  }

  test("code calling another contract's operation is proven from that contract's promise alone") {
    val w = workflow(callsKb)
    val g = w.generate
    assertEquals(g.callees(againC).map(_.id), List("PickPromise"))
    assert(g.obligation(againC, "impl").exists(_.statement.contains("h_PickPromise")), g.obligations(againC))
    val r = w.check()
    assert(r.forall(_._2.status.toString == "proven"), r)
    assertEquals(result(of(r, "Again"), "impl").map(_.status.toString), Some("proven"))
    // the root of the code: PickPromise's code is proven too, so nothing is trusted
    assertEquals(g.trusted, Nil)
    assertEquals(result(of(r, "PickedAgain"), "root_impl").map(_.status.toString), Some("proven"), of(r, "PickedAgain"))
    // its examples are evaluated in Lean, the call standing for PickPromise's proven code
    assert(of(r, "Again").obligations.exists(o => o.name.startsWith("eval_") && o.status.toString == "proven"), of(r, "Again"))
  }

  test("a callee's parameters the caller does not read are bound once, beside the caller's; its examples need no wiring") {
    val kb = KnowledgeBase("Capped", idea = "IDEA.md")(pickedLong, longPick, capped)
      .implementProven(capped)(cappedOnes).implementProven(longPick)(viaCapped)
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val impl = w.generate.obligation(longPick, "impl").get.statement
    // one cap for every call: not a cap per call, which no single function could meet
    assert(impl.contains("(maxPages : Int)") && impl.contains("(h_Capped : (Capped.Capped.claim"), impl)
    val c = of(w.check(), "LongPick")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(c.obligations.filter(_.name.startsWith("eval_")).forall(_.status.toString == "proven"), c)
    // in Scala the examples run Capped's code for the call
    assert(kb.exampleResults(longPick).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), kb.exampleResults(longPick))
    // a running service calls Capped's service
    val s = kb.service(longPick)(minPages.bind(100), maxPages.bind(500))
    assertEquals(s(List(Book("Long", 300), Book("Huge", 900)), 5), List(Book("Long", 300)))
  }

  test("membership through a list's set is proven, and its examples are evaluated in Lean") {
    val r = workflow(keepKb).check()
    val c = of(r, "Keep")
    assertEquals(c.status.toString, "proven", c)
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(c.obligations.filter(_.name.startsWith("eval_")).forall(_.status.toString == "proven") && c.obligations.exists(_.name.startsWith("eval_")), c)
    assertEquals(result(of(r, "KeptOnShelf"), "root_impl").map(_.status.toString), Some("proven"), of(r, "KeptOnShelf"))
  }

  test("state kept in a Map is proven, down to the code, and its examples are evaluated in Lean") {
    val w = workflow(KnowledgeBase("Counter", idea = "IDEA.md")(counts, bump).implementProven(bump)(bumped))
    val r = w.check()
    val c = of(r, "Bump")
    assertEquals(c.status.toString, "proven", c)
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assertEquals(List("complete", "root_impl").map(n => result(of(r, "Counts"), n).map(_.status.toString)), List(Some("proven"), Some("proven")), of(r, "Counts"))
    // maps compared key by key; one that differs at a key the call does not name is not found
    assertEquals(c.obligations.filter(_.name.startsWith("eval_")).map(_.status.toString), List("proven", "proven", "unevaluated"), c)
  }
