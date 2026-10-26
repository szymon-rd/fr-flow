package frflow

import frflow.fixtures.*
import frflow.testing.Plan

/** Plain code tested against its contract: the property is the contract's formula, the cases come from the types. */
class TestingSuite extends munit.FunSuite:
  private val few = TestSettings(cases = 300, seed = 3)

  test("code that meets its contract passes, and every part of the contract is reached") {
    val r = shelfKb.testedWith(few).test(pick).get
    assertEquals(r.failure, None)
    assert(r.coverage.nonEmpty)
    assert(r.passed, r.coverage.filter(_.held == 0).mkString("; "))
    assertEquals(r.against, "Pick")
  }

  test("FRFLOW_SEED replaces the seed: a number, or fresh; anything else keeps the settings") {
    val s = TestSettings(cases = 50, seed = 3)
    assertEquals(TestSettings.inForce(s, Some("42")), s.copy(seed = 42))
    // fresh: one new seed for the run, the same each time it is asked
    assertNotEquals(TestSettings.inForce(s, Some("fresh")).seed, 3L)
    assertEquals(TestSettings.inForce(s, Some("fresh")), TestSettings.inForce(s, Some("fresh")))
    assertEquals(TestSettings.inForce(s, Some("soon")), s)
    assertEquals(TestSettings.inForce(s, None), s)
  }

  test("a seeded bug is found, and the case is shrunk to its smallest") {
    // Off by one: a book of exactly the asked length is left on the shelf.
    val buggy = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick)*).testedWith(few)
      .implement(pick)((shelf, n) => shelf.filter(_.pages > minPages.value))
    val f = buggy.test(pick).get.failure.getOrElse(fail("the bug was not found"))
    // One book, at the length asked, the rest as small as the generator allows; the inputs by the contract's names, the
    // result said once, by why it fails.
    assert(f.shown.matches("""shelf = List\(Book\("", (-?\d+)\)\), n = 0, given minPages = \1"""), f.shown)
    assertEquals(f.why, "returned List(), which Pick forbids")
  }

  test("the same seed gives the same cases; a failing case replays first") {
    val buggy = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick)*).testedWith(few)
      .implement(pick)((shelf, n) => shelf.filter(_.pages > minPages.value))
    val a = buggy.test(pick).get.failure.get
    val b = buggy.test(pick).get.failure.get
    assertEquals(a, b)
    // Replayed (even under another seed), the case that failed is the first one tried.
    val again = buggy.testedWith(TestSettings(300, seed = 99)).test(pick, replay = List(Testing.Replay(a.seed, a.index, a.size))).get.failure
    assertEquals(again.map(f => (f.seed, f.index)), Some((a.seed, a.index)))
  }

  test("a part no case reaches is said, not passed") {
    // Every book is long: `b.pages >= minPages implies …` never fails to hold its premise, and the other way never holds.
    val lazyGen = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick)*).testedWith(few)
      .implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))
      .generating(Gen.listOf(Gen.const(Book("Short", 1))).describedAs("only short books"))
      .generating(Gen.const(100).describedAs("always 100"))
    val r = lazyGen.test(pick).get
    assertEquals(r.failure, None)
    // The given generators make most values; the derived one still makes a quarter, so the parts are reached.
    assert(r.notes.exists(_.contains("only short books")), r.notes.mkString("; "))
  }

  test("a given generator that never makes the examples' values is said; they stay seeds") {
    val narrow = shelfKb.testedWith(few).generating(Gen.oneOf(Book("A", 1), Book("B", 2)))
    val r = narrow.test(pick).get
    assert(r.notes.exists(n => n.contains("never come from the given generator") && n.contains("Book(\"Long\", 300)")), r.notes.mkString("; "))
  }

  test("generated values cover the types: numbers, strings, lists, options, enums, tables") {
    val plan = Plan(Map.empty, Map.empty, Nil, Map.empty)
    val d = Draw(java.util.SplittableRandom(5), 6, plan)
    val shelves = List.fill(200)(d.value(summon[LeanType[Shelf]]))
    assert(Set("Top", "Bottom", "Box").forall(c => shelves.exists(_.toString.startsWith(c))), shelves.distinct.toString)
    val f = d.value(summon[LeanType[String => Option[Int]]]).asInstanceOf[String => Option[Int]]
    assertEquals(f("no such key ever"), None)
    val ns = List.fill(200)(d.value(summon[LeanType[Long]]))
    assert(ns.forall(_.isInstanceOf[Long]))
  }

  test("a proven define has nothing to test; code beside one is tested against it") {
    assertEquals(shelfWith(pick).implementProven(pick)(longOnes).test(pick), None)
    val beside = shelfWith(pick).testedWith(few).implementProven(pick)(longOnes, (shelf, n) => shelf.filter(_.pages > minPages.value))
    val f = beside.test(pick).get.failure.get
    assert(f.why.contains("where the proven define longOnes returns"), f.why)
  }
