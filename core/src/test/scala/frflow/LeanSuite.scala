package frflow

import frflow.fixtures.*
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** End to end against Lean. Skipped when `lake` is not available. */
class LeanSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  private lazy val kernel: Path =
    Iterator.iterate(Paths.get(sys.props("user.dir")).toAbsolutePath)(_.getParent).takeWhile(_ != null)
      .map(_.resolve("lean")).find(p => Files.exists(p.resolve("FrFlow.lean"))).getOrElse(fail("kernel not found"))

  private def workflow(kb: KnowledgeBase): Workflow =
    assume(Lake(Paths.get(".")).available, "lake is not available")
    Workflow(kb, Workspace(Files.createTempDirectory("frflow"), kernel.toString))

  private def statuses(r: List[(Node[?], NodeCheck)]) = r.map((n, c) => n.id -> c.status)

  test("a generic knowledge base is proven end to end by automation") {
    val w = workflow(shelfKb)
    val r = w.check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Listed" -> "proven", "Books" -> "proven", "Pick" -> "proven"))
    assert(r.flatMap(_._2.obligations).filter(o => !o.isLimit && !o.isEvaluation).forall(_.detail == "auto"), r)
    assert(r.flatMap(_._2.axioms).forall(Lean.allowedAxioms))
    val links = w.baseSnapshot("nodes").get.arr.map(n => n("id").flatMap(_.str).get -> n("link").flatMap(_("detail")).flatMap(_.str))
    assertEquals(links.toList, List("OnlyGood" -> None, "Listed" -> Some("auto"), "Books" -> Some("instantiation"), "Pick" -> Some("auto")))
  }

  test("a refinement that does not imply its parent is not accepted") {
    val r = workflow(sloppyKb).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Sloppy" -> "open"))
    assert(r(1)._2.obligations.head.detail.contains("frflow_auto found no proof"), r(1)._2.obligations)
  }

  private val feasible = "  unfold Obl.feasible\n  exact ⟨fun x => x * x, by simp [frflow_defs]⟩"

  test("an obligation automation cannot prove is proven in a separate file") {
    val w = workflow(squareKb)
    assertEquals(statuses(w.check()), List("NonNegative" -> "proven", "Squares" -> "open"))
    assert(w.scaffold(squares))
    assertEquals(w.check(Some("Squares")).head._2.obligations.head.detail, "uses sorry")

    val file = w.ws.lean.resolve(w.generate.proofsPath("Squares"))
    def edit(f: String => String) = Files.writeString(file, f(Files.readString(file)))
    edit(_.replace("  unfold Obl.link\n  sorry",
      """  unfold Obl.link
        |  intro m h
        |  simp only [frflow_defs] at *
        |  intro x
        |  rw [h x]
        |  rcases Int.le_total 0 x with hx | hx
        |  · exact Int.mul_nonneg hx hx
        |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
        |    simpa [Int.neg_mul_neg] using this""".stripMargin))
    // an authored link needs a witness that something meets the node
    assertEquals(w.check(Some("Squares")).head._2.obligations.find(_.name == "feasible").map(_.status), Some("open"))
    edit(_.replace("  unfold Obl.feasible\n  sorry", feasible))
    // ...and that the root says something under it: some model fails it
    val noWitness = w.check(Some("Squares")).head._2
    assertEquals(noWitness.obligations.find(_.name == "nontrivial").map(_.status), Some("open"), noWitness)
    assertEquals(w.link(squares)("status").flatMap(_.str), Some("open"))
    edit(_.replace("  unfold Obl.nontrivial\n  sorry", "  unfold Obl.nontrivial\n  exact ⟨fun _ => -1, by simp [frflow_defs]⟩"))
    val proven = w.check(Some("Squares")).head._2
    assertEquals(w.link(squares)("status").flatMap(_.str), Some("proven"))
    assertEquals((proven.status, proven.obligations.head.detail), ("proven", "authored"), proven)
    assertEquals(proven.obligations.find(_.name == "feasible").map(_.status), Some("proven"))
    assert(!Files.readString(w.ws.lean.resolve(w.generate.autoPath("Squares"))).contains("theorem link"))

    // a proof of something weaker does not count
    edit(src => src.replaceAll("(?s)theorem link : Obl.link := by.*?(?=\nend )", "theorem link : True := trivial\n"))
    assertEquals(w.check(Some("Squares")).head._2.obligations.head.status, "failed")
  }

  test("proofs may share lemmas, which are filtered and replayed like them") {
    val w = workflow(squareKb)
    w.check()
    assert(w.scaffold(squares))
    val file = w.ws.lean.resolve(w.generate.proofsPath("Squares"))
    val lemmas = w.ws.lean.resolve(w.generate.lemmasPath)
    def lemma(body: String) = Files.writeString(lemmas,
      s"import FrFlow\n\nnamespace Square.Lemmas\n\n$body\n\nend Square.Lemmas\n")
    lemma("""theorem sq (x : Int) : 0 ≤ x * x := by
            |  rcases Int.le_total 0 x with hx | hx
            |  · exact Int.mul_nonneg hx hx
            |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
            |    simpa [Int.neg_mul_neg] using this""".stripMargin)
    val src = Files.readString(file)
    Files.writeString(file, src.replaceFirst("import ", "import Proofs.Square.Lemmas\nimport ")
      .replace("  unfold Obl.link\n  sorry", "  unfold Obl.link\n  intro m h\n  simp only [frflow_defs] at *\n  intro x\n  rw [h x]\n  exact Square.Lemmas.sq x")
      .replace("  unfold Obl.feasible\n  sorry", feasible))
    val proven = w.check(Some("Squares")).head._2
    assertEquals((proven.status, proven.obligations.head.detail), ("proven", "authored"), proven)
    // a lemma file gets the same filter as a proof file
    lemma("axiom sq (x : Int) : 0 ≤ x * x")
    val bad = w.check(Some("Squares")).head._2
    assertEquals(bad.status, "failed", bad)
    assert(bad.messages.exists(_.contains("not allowed in lean/Proofs/Square/Lemmas.lean")), bad.messages)
  }

  test("a refinement whose abs alone makes the parent hold is vacuous") {
    val vacuous = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("NoPick", "Nothing is ever wrong.", why = "w")(
      abs = pick => (l, n) => Nil, spec = pick => true)
    val r = workflow(KnowledgeBase("Vac", idea = "IDEA.md")(onlyGood, vacuous)).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "NoPick" -> "failed"))
    assert(r(1)._2.obligations.head.detail.startsWith("vacuous"), r(1)._2.obligations)
  }

  test("a node whose abs alone makes the root hold is reported, though its link to the parent is real") {
    // abs keeps only good items (what the root asks); the spec only says items come from the list.
    val filtered = listed.refine[(List[Item.T], Int) => List[Item.T]]("Filtered", "Picked items come from the list.", why = "w")(
      abs = pick => (l, n) => pick(l, n).filter(x => good(x)),
      spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x))))
    val r = workflow(KnowledgeBase("RootTriv", idea = "IDEA.md")(onlyGood, listed, filtered)).check()
    val c = r.find(_._1.id == "Filtered").get._2
    assertEquals(c.status, "failed", c)
    assert(c.obligations.head.detail.contains("the root holds"), c.obligations)
  }

  test("an invariant a contract keeps is proven from its post, or left open") {
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b))
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "w")((asked, picked) => picked <= asked)
    val inName = Node.invariant[List[Book], Book]("InName", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b))
    val kept = pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b)))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
      // a view that shows the rule only what it accepts keeps nothing
      .keeps(inName)((shelf, n, picked) => picked.filter(b => shelf.contains(b)).map(b => (shelf, b)))
    val w = workflow(KnowledgeBase("Inv", idea = "IDEA.md")(onlyGood, listed, books, kept, fromShelf, atMostN, inName))
    val c = w.check().find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.find(_.name == "inv_FromShelf").map(_.status), Some("proven"), c)
    // the view lists every book picked, with the shelf it was asked of
    assertEquals(c.obligations.find(_.name == "cover_FromShelf").map(_.status), Some("proven"), c)
    // a rule about numbers is not about what the result holds
    assertEquals(c.obligations.find(_.name == "cover_AtMostN"), None, c)
    assertEquals(c.obligations.find(_.name == "inv_AtMostN").map(_.status), Some("open"), c)
    assertEquals(c.obligations.find(_.name == "inv_InName").map(_.status), Some("failed"), c)
    // an authored proof that uses sorry is not a proof, however Lean prints its axioms
    Files.createDirectories(w.ws.lean.resolve(w.generate.proofsPath("Pick")).getParent)
    Files.writeString(w.ws.lean.resolve(w.generate.proofsPath("Pick")),
      """import FrFlowGen.Inv.Pick.Spec
        |
        |set_option autoImplicit false
        |noncomputable section
        |open Classical
        |
        |namespace Inv.Pick.Proofs
        |open Inv.Pick
        |
        |theorem inv_AtMostN : Obl.inv_AtMostN := by
        |  unfold Obl.inv_AtMostN
        |  sorry
        |
        |end Inv.Pick.Proofs
        |""".stripMargin)
    val sorried = w.check(Some("Pick")).head._2
    assertEquals(sorried.obligations.find(_.name == "inv_AtMostN").map(r => (r.status, r.detail)), Some(("open", "uses sorry")), sorried)
  }

  test("a view that leaves out what the result holds keeps nothing, however it hides the condition") {
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b))
    val hidden = pick.keeps(fromShelf)((shelf, n, picked) => onShelf(shelf, picked).map(b => (shelf, b)))
    val c = workflow(KnowledgeBase("Hidden", idea = "IDEA.md")(onlyGood, listed, books, hidden, fromShelf)).check().find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.find(_.name == "cover_FromShelf").map(_.status), Some("open"), c)
  }

  test("Lean evaluates each example as Scala does, and a disagreement fails the node") {
    val c = workflow(shelfKb).check().find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.filter(_.name.startsWith("eval")).map(o => o.name -> o.status),
      List("eval_0" -> "proven", "eval_1" -> "proven", "eval_2" -> "proven"), c)
    // A parameter that is no fixed value: Lean is given one value of it, Scala's post reads another.
    var flip = false
    val unstable = books.contract[List[Book], Int, List[Book]]("Unstable", "Picking returns only long enough books.", why = "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
      .examples(minPages.bind { flip = !flip; if flip then 100 else 10 })(
        expect(List(Book("Mid", 50)), 5, List(Book("Mid", 50)), "a book of 50 pages"),
        reject(List(Book("Mid", 50)), 5, List(Book("Other", 50)), "not a book from the shelf"))
    val u = workflow(KnowledgeBase("Unstable", idea = "IDEA.md")(onlyGood, listed, books, unstable)).check().find(_._1.id == "Unstable").get._2
    assertEquals(u.status, "failed", u)
    assertEquals(u.obligations.find(_.name == "eval_0").map(_.status), Some("failed"), u)
    assertEquals(u.obligations.find(_.name == "eval_1").map(_.status), Some("proven"), u)
    assert(u.messages.head.contains("Lean and Scala disagree"), u.messages)
  }

  test("probes near the examples find a translation bug the examples miss") {
    def kb(d: Def[(List[BigInt], BigInt) => List[BigInt]]) = KnowledgeBase("Probe", idea = "IDEA.md")(floorRoot, floorKeep).implementProven(floorKeep)(d)
    val good = workflow(kb(keepAtLeast)).check().find(_._1.id == "FloorKeep").get._2
    assertEquals(good.status, "proven", good)
    assert(good.obligations.count(o => o.name.startsWith("probe") && o.status == "proven") >= 3, good.obligations)
    // A translation bug, injected: the Lean of the code says > where the Scala says >=. Lean still proves
    // the code meets the contract, and the examples agree; a probe at the boundary does not.
    val l = keepAtLeast.lifted
    assert(l.body.contains("≥"), l.body)
    val wrong = Def(keepAtLeast.name, new Lifted(l.value, l.params, l.result, l.body.replace("≥", ">"), l.source, l.types, l.opaques,
      l.paramRefs, () => l.defs, () => l.paramObjects, () => l.opaqueObjects))
    val bad = workflow(kb(wrong)).check().find(_._1.id == "FloorKeep").get._2
    assertEquals(bad.status, "failed", bad)
    assert(bad.obligations.filter(_.name.startsWith("eval")).forall(_.status == "proven"), bad.obligations)
    assert(bad.obligations.exists(o => o.name.startsWith("probeImpl") && o.status == "failed"), bad.obligations)
  }

  test("a proven implementation's results are evaluated in Lean too") {
    val kb = KnowledgeBase("ImplEval", idea = "IDEA.md")(onlyGood, listed, books, pick).implementProven(pick)(longOnes)
    val c = workflow(kb).check().find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.filter(_.name.startsWith("evalImpl")).map(_.status), List.fill(3)("proven"), c)
  }

  test("an implementation written as a define is proven to keep its contract") {
    val kb = KnowledgeBase("Impl", idea = "IDEA.md")(onlyGood, listed, books, pick).implementProven(pick)(longOnes)
    assert(kb.exampleResults(pick).forall(_.implementation.contains("ok")), kb.exampleResults(pick))
    val r = workflow(kb).check()
    val c = r.find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.find(_.name == "impl").map(_.status), Some("proven"), c)
    // one that can return a short book is not proven
    val w2 = workflow(KnowledgeBase("Impl2", idea = "IDEA.md")(onlyGood, listed, books, pick).implementProven(pick)(anyOnes))
    val bad = w2.check()
    assertEquals(bad.find(_._1.id == "Pick").get._2.obligations.find(_.name == "impl").map(_.status), Some("open"))
    // scaffold stubs what is open, the implementation, and leaves the proven link to automation
    assert(w2.scaffold(pick))
    val src = Files.readString(w2.ws.lean.resolve(w2.generate.proofsPath("Pick")))
    assert(src.contains("theorem impl : Obl.impl") && !src.contains("theorem link"), src)
    val again = w2.check(Some("Pick")).head._2
    assertEquals(again.obligations.find(_.name == "link").map(_.detail), Some("auto"), again)
    assertEquals(again.obligations.find(_.name == "impl").map(_.status), Some("open"), again)
  }

  test("a contract with a signature of its own is proven through its abs") {
    // the best book alone, by title: as the parent's model, the list of that one book
    val best = books.contractVia[List[Book], String, Option[Book]]("Best", "The book named is picked, if it is long enough.", why = "w")(
      abs = f => (shelf, n) => shelf.filter(b => f(shelf, b.title) == Some(b)))(
      (shelf, title, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value && b.title == title))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300)), "Long", Some(Book("Long", 300)), "the long book, named"),
        expect(List(Book("Short", 20)), "Short", None, "a short book is never picked"),
        reject(List(Book("Short", 20)), "Short", Some(Book("Short", 20)), "not a short one"))
    val r = workflow(KnowledgeBase("Via", idea = "IDEA.md")(onlyGood, listed, books, best)).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Listed" -> "proven", "Books" -> "proven", "Best" -> "proven"), r)
  }

  test("a node no model meets is reported, so it cannot make everything below it hold") {
    val never = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Never", "Nothing is ever picked.", why = "w")(
      abs = pick => pick, spec = pick => false)
    val r = workflow(KnowledgeBase("Unsat", idea = "IDEA.md")(onlyGood, never)).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Never" -> "failed"))
    assert(r(1)._2.obligations.head.detail.startsWith("unsatisfiable"), r(1)._2.obligations)
  }

  test("a contract's code may call another contract: it is proven from that contract's promise alone") {
    val kb = KnowledgeBase("Calls", idea = "IDEA.md")(onlyGood, listed, books, pick, again)
      .implementProven(pick)(longOnes).implementProven(again)(viaPick)
    val w = workflow(kb)
    val g = w.generate
    assertEquals(g.callees(again).map(_._2.id), List("Pick"))
    assert(g.obligations(again).find(_.name == "impl").exists(_.statement.contains("h_pickCall")), g.obligations(again))
    val r = w.check()
    val c = r.find(_._1.id == "Again").get._2
    assertEquals(c.status, "proven", c)
    assertEquals(c.obligations.filter(o => Set("impl", "root_impl")(o.name)).map(_.status), List("proven", "proven"), c)
    // its examples are evaluated in Lean, the call standing for Pick's proven code
    assert(c.obligations.exists(o => o.name.startsWith("eval_") && o.status == "proven"), c)
    // it rests on Pick: a change to Pick's meaning reviews it
    assertEquals(w.restsOn(again).map(_.id), List("Pick"))
  }

  test("a callee's parameters the caller does not read are bound once, beside the caller's; its examples need no wiring") {
    val kb = KnowledgeBase("Capped", idea = "IDEA.md")(onlyGood, listed, books, capped, longPick)
      .implementProven(capped)(cappedOnes).implementProven(longPick)(viaCapped)
    val w = workflow(kb)
    val impl = w.generate.obligations(longPick).find(_.name == "impl").get.statement
    // one cap for every call: not a cap per call, which no single function could meet
    assert(impl.contains("(maxPages : Int) (h_cappedCall : ∀ (y0"), impl)
    val c = w.check().find(_._1.id == "LongPick").get._2
    assertEquals(c.obligations.filter(o => Set("impl", "root_impl")(o.name)).map(_.status), List("proven", "proven"), c)
    assert(c.obligations.filter(_.name.startsWith("eval_")).forall(_.status == "proven"), c)
    // in Scala the examples run Capped's code for the call
    assert(kb.exampleResults(longPick).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), kb.exampleResults(longPick))
    // a running service calls Capped's service
    val s = kb.service(longPick)(minPages.bind(100), maxPages.bind(500))
    assertEquals(s(List(Book("Long", 300), Book("Huge", 900)), 5), List(Book("Long", 300)))
  }

  test("code using flatMap and take is proven to meet its contract, and evaluated in Lean") {
    val c = workflow(KnowledgeBase("Firsts", idea = "IDEA.md")(onlyGood, listed, books, pick).implementProven(pick)(firstLong)).check().find(_._1.id == "Pick").get._2
    assertEquals(c.obligations.filter(o => Set("impl", "root_impl")(o.name)).map(_.status), List("proven", "proven"), c)
    assert(c.obligations.filter(_.name.startsWith("eval_")).forall(_.status == "proven"), c)
  }

  test("a port has no parent: Lean proves its check follows from its post, and service runs the check") {
    val kb = KnowledgeBase("Ports", idea = "IDEA.md")(shelfPort).implementProven(shelfPort)(fromService, (shelf, n) => shelf.filter(_.pages >= minPages.value))
    val c = workflow(kb).check().find(_._1.id == "ShelfPort").get._2
    assertEquals(c.status, "proven", c)
    assertEquals(c.obligations.filter(o => Set("check", "impl", "root_impl")(o.name)).map(o => o.name -> o.status).toSet,
      Set("check" -> "proven", "impl" -> "proven", "root_impl" -> "proven"), c)
    // the check, not the post: a book off the shelf passes it, a short book does not
    val off = KnowledgeBase("Ports", idea = "IDEA.md")(shelfPort).implement(shelfPort)((shelf, n) => List(Book("Elsewhere", 500)))
    assertEquals(off.service(shelfPort)(minPages.bind(100))(Nil, 1), List(Book("Elsewhere", 500)))
    val short = KnowledgeBase("Ports", idea = "IDEA.md")(shelfPort).implement(shelfPort)((shelf, n) => List(Book("Short", 20)))
    intercept[ContractViolation](short.service(shelfPort)(minPages.bind(100))(Nil, 1))
  }

  test("a recorded result that does not hold is found when it is proven again") {
    val w = workflow(sloppyKb)
    assert(w.check().find(_._1.id == "Sloppy").exists(_._2.status != "proven"))
    // a cache that says otherwise: Sloppy recorded as proven, for what it is now
    val forged = w.checks.map((id, c) => id -> (if id == "Sloppy" then c.copy(status = "proven", obligations = c.obligations.map(_.copy(status = "proven"))) else c))
    Checks.save(w.ws.checksFile, forged)
    assertEquals(w.current(sloppy).map(_.status), Some("proven"))
    assertEquals(w.sample(1.0), Set("OnlyGood", "Sloppy"))
    assertNotEquals(w.check(verify = Set("Sloppy")).find(_._1.id == "Sloppy").get._2.status, "proven")
  }

  test("a node proven again is elaborated again, not taken from Lean's build cache") {
    val w = workflow(shelfKb)
    w.check()
    def built() = scala.util.Using.resource(Files.walk(w.ws.lean.resolve(".lake/build")))(_.iterator.asScala.toList)
      .filter(p => Files.isRegularFile(p) && p.toString.contains("FrFlowGen/Shelf/Listed/")).map(p => p -> Files.getLastModifiedTime(p)).toMap
    val before = built()
    assert(before.nonEmpty)
    Thread.sleep(1100)
    assertEquals(w.check(verify = Set("Listed")).find(_._1.id == "Listed").get._2.status, "proven")
    val after = built()
    assert(before.keySet.forall(p => after.get(p).exists(_.compareTo(before(p)) > 0)), (before, after))
  }

  test("another project's contract is proven here too, as it stands here") {
    val shelf = workflow(shelfKb)
    val reader = Workflow(readerKb(shelf.ws.root.toString), Workspace(Files.createTempDirectory("reader"), kernel.toString))
    val r = reader.check()
    assertEquals(r.map((n, c) => n.id -> c.status).toMap.get("Pick"), Some("proven"), r)
    assertEquals(r.map((n, c) => n.id -> c.status).toMap.get("ReadingList"), Some("proven"), r)
  }

  test("a root doing nothing meets is unproven, unless it says why it only forbids") {
    val w = workflow(KnowledgeBase("Guard", idea = "IDEA.md")(onlyGood))
    w.check()
    val n = w.annotated("nodes").get.arr.find(_("id").flatMap(_.str).contains("OnlyGood")).get
    assert(Decisions.unproven(n).exists(_.contains("doing nothing meets it")), Decisions.unproven(n))
    val guard = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", onlyGood.statement, onlyGood.why, safety = "picking is a guard here: what is picked is the caller's choice")(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w2 = workflow(KnowledgeBase("Guard", idea = "IDEA.md")(guard))
    w2.check()
    val n2 = w2.annotated("nodes").get.arr.find(_("id").flatMap(_.str).contains("OnlyGood")).get
    assert(Decisions.unproven(n2).isEmpty, Decisions.unproven(n2))
    assert(n2("limits").exists(_.arr.exists(_.str.exists(_.contains("says only what must not happen")))), n2("limits"))
  }

  test("state kept in a Map is proven, down to the code, and its examples are evaluated in Lean") {
    val w = workflow(KnowledgeBase("Counter", idea = "IDEA.md")(counts, bump).implementProven(bump)(bumped))
    val c = w.check().find(_._1.id == "Bump").get._2
    assertEquals(c.status, "proven", c)
    assertEquals(c.obligations.filter(o => Set("link", "impl", "root_impl")(o.name)).map(_.status), List("proven", "proven", "proven"), c)
    // maps compared key by key; one that differs at a key the call does not name is not found
    assertEquals(c.obligations.filter(_.name.startsWith("eval_")).map(_.status), List("proven", "proven", "unevaluated"), c)
  }

