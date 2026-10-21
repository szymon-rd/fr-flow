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
    assert(r.flatMap(_._2.obligations).forall(_.detail == "auto"))
    assert(r.flatMap(_._2.axioms).forall(Lean.allowedAxioms))
    val links = w.snapshot("nodes").get.arr.map(n => n("id").flatMap(_.str).get -> n("link").flatMap(_("detail")).flatMap(_.str))
    assertEquals(links.toList, List("OnlyGood" -> None, "Listed" -> Some("auto"), "Books" -> Some("instantiation"), "Pick" -> Some("auto")))
  }

  test("a refinement that does not imply its parent is not accepted") {
    val r = workflow(sloppyKb).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Sloppy" -> "open"))
    assert(r(1)._2.obligations.head.detail.contains("frflow_auto found no proof"), r(1)._2.obligations)
  }

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
    val proven = w.check(Some("Squares")).head._2
    assertEquals((proven.status, proven.obligations.head.detail), ("proven", "authored"))
    assert(!Files.readString(w.ws.lean.resolve(w.generate.autoPath("Squares"))).contains("theorem link"))

    // a proof of something weaker does not count
    edit(src => src.replaceAll("(?s)theorem link : Obl.link := by.*?(?=\nend )", "theorem link : True := trivial\n"))
    assertEquals(w.check(Some("Squares")).head._2.obligations.head.status, "failed")
  }

  test("decisions are bound to what was decided, and to the decided parent") {
    val w = workflow(shelfKb)
    shelfKb.nodes.foreach(w.accept(_, "dev", "", Nil))
    assert(shelfKb.nodes.forall(w.decision(_) == "accepted"))
    val reworded = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Every picked item is in the list and is good.", why = "Same.")(
      abs = pick => pick,
      spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val books2 = reworded.instantiate[(List[Book], Int) => List[Book]]("Books", books.statement, books.why)(books.substs*)
    val w2 = Workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, reworded, books2), w.ws)
    assertEquals(w2.decision(onlyGood), "accepted")
    assertEquals(w2.decision(reworded), "changed")
    assertEquals(w2.decision(books2), "parent-changed")
  }
