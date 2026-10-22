package frflow

import frflow.fixtures.*
import java.nio.file.{Files, Path, Paths}

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
    assert(r.flatMap(_._2.obligations).filter(o => o.name != "idle" && !o.name.startsWith("eval")).forall(_.detail == "auto"), r)
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
    val proven = w.check(Some("Squares")).head._2
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
    val bad = workflow(KnowledgeBase("Impl2", idea = "IDEA.md")(onlyGood, listed, books, pick).implementProven(pick)(anyOnes)).check()
    assertEquals(bad.find(_._1.id == "Pick").get._2.obligations.find(_.name == "impl").map(_.status), Some("open"))
  }

  test("an assumed link is decided by reading, and every root theorem resting on it names it") {
    val assumedSquares = nonNegative.refine[BigInt => BigInt]("Squares", "The result is the square of the input.", why = "Squares are never negative.",
      assume = true)(abs = f => f, spec = f => forall((x: BigInt) => f(x) == x * x))
    val r = workflow(KnowledgeBase("Assumed", idea = "IDEA.md")(nonNegative, assumedSquares)).check()
    val c = r.find(_._1.id == "Squares").get._2
    assertEquals(c.status, "proven", c)
    assertEquals(c.obligations.head.status, "assumed")
    assert(c.axioms.contains("Assumed.Squares.Auto.link"), c.axioms)
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

