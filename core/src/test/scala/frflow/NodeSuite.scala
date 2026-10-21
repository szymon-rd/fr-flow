package frflow

import frflow.fixtures.*

/** Nodes, Lean generation, and enforcement on the shelf fixture. */
class NodeSuite extends munit.FunSuite:

  private val g = Generate(shelfKb)

  test("the knowledge base is well formed") {
    assertEquals(shelfKb.problems, Nil)
    assertEquals(shelfKb.ordered.map(_.id), List("OnlyGood", "Listed", "Books", "Pick"))
    assertEquals(shelfKb.params.map(_.name), List("good", "minPages"))
  }

  test("a contract must have its parent's model type") {
    assert(compileErrors("""frflow.fixtures.onlyGood.contract[Int, Int, Int]("C", "c")((a, b, r) => true)""").nonEmpty)
  }

  test("contexts: generic nodes take opaque types and parameters; instantiation removes them") {
    assertEquals(g.nodeCtx(listed) match { case c => (c.opaques, c.params) }, (List("Item"), List("good")))
    assertEquals(g.nodeCtx(books) match { case c => (c.opaques, c.params) }, (Nil, List("minPages")))
    assertEquals(g.theta(books), "(Item := Book) (good := (s_good minPages))")
  }

  test("refine and contract nodes have one obligation; root and instantiate none") {
    assertEquals(g.obligation(onlyGood), None)
    assertEquals(g.obligation(books), None)
    assertEquals(g.obligation(listed).map(_.statement),
      Some("∀ (Item : Type) (good : (Item → Prop)), ∀ (m : ((List Item) → Int → (List Item))), spec Item good m → Shelf.OnlyGood.spec Item good (abs Item good m)"))
    assertEquals(g.obligation(pick).map(_.statement),
      Some("∀ (minPages : Int), ∀ (m : (List Book) → Int → (List Book)), spec minPages m → Shelf.Books.spec minPages m"))
  }

  test("every node gets a root theorem") {
    kb(shelfKb).foreach(n => assert(g.theorems(n).contains("theorem root"), n.id))
    assert(g.theorems(books).contains("Shelf.Listed.root (Item := Book) (good := (s_good minPages))"))
  }

  private def kb(k: KnowledgeBase) = k.nodes

  test("an enforced implementation returns results that meet the contract") {
    val ok = pick.enforce((shelf, n) => shelf.filter(_.pages >= 100).take(n))(minPages.bind(100))
    assertEquals(ok(List(Book("a", 50), Book("b", 150)), 5), List(Book("b", 150)))
  }

  test("an enforced implementation that breaks the contract fails closed") {
    val bad = pick.enforce((shelf, n) => shelf.take(n))(minPages.bind(100))
    intercept[ContractViolation](bad(List(Book("a", 50)), 1))
  }

  test("parameters must be bound to evaluate a contract") {
    val unbound = pick.enforce((shelf, n) => shelf)()
    intercept[IllegalStateException](unbound(List(Book("a", 500)), 1))
  }
