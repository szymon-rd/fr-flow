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
    val links = w.baseSnapshot("nodes").get.arr.map(n => n("id").flatMap(_.str).get -> n("link").flatMap(_("detail")).flatMap(_.str))
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

  test("a node no model meets is reported, so it cannot make everything below it hold") {
    val never = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Never", "Nothing is ever picked.", why = "w")(
      abs = pick => pick, spec = pick => false)
    val r = workflow(KnowledgeBase("Unsat", idea = "IDEA.md")(onlyGood, never)).check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "Never" -> "failed"))
    assert(r(1)._2.obligations.head.detail.startsWith("unsatisfiable"), r(1)._2.obligations)
  }

