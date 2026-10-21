package frflow

import frflow.fixtures.*

/** The macro: Scala in, Lean out, with the Scala still executable. */
class LiftSuite extends munit.FunSuite:

  test("case classes: construction, fields, copy") {
    val c = Lifted((b: Book) => b.copy(pages = b.pages + 1) == Book(b.title, 2))
    assertEquals(c.body, "({ b with pages := (b.pages + 1) } = (Book.mk b.title 2))")
    assertEquals(c.params, List("b" -> "Book"))
    assert(c.types.exists(t => t.name == "Book" && t.lean.contains("pages : Int")))
    assert(c.value(Book("x", 1)))
    assert(!c.value(Book("x", 5)))
  }

  test("enums and match") {
    assertEquals(where.lifted.body,
      "(match s with | Shelf.Top => \"top\" | Shelf.Bottom => \"bottom\" | Shelf.Box l => l)")
    assertEquals(where(Shelf.Box("b")), "b")
    assert(where.lifted.types.exists(_.lean.contains("| Box (label : String)")))
  }

  test("opaque types and parameters become Lean variables") {
    val c = Lifted((x: Item.T) => good(x))
    assertEquals(c.params, List("x" -> "Item"))
    assertEquals(c.body, "(good x)")
    assertEquals(c.opaques, List("Item"))
    assertEquals(c.paramRefs, List("good" -> "(Item → Prop)"))
    assertEquals(c.paramObjects.map(_.name), List("good"))
  }

  test("tuple fields follow Lean's nesting: A × B × C is A × (B × C)") {
    val c = Lifted((t: (Int, Int, Int)) => t._2 * 10 + t._3)
    assertEquals(c.body, "((t.2.1 * 10) + t.2.2)")
    assertEquals(c.value((1, 2, 3)), 23)
    assertEquals(Lifted((t: (Int, Int)) => t._1 - t._2).body, "(t.1 - t.2)")
  }

  test("patterns Lean would read as catch-alls are refused") {
    assert(compileErrors("frflow.Lifted((o: Option[Boolean]) => o match { case Some(true) => 1; case _ => 2 })")
      .contains("matching on true or false"))
    assert(compileErrors("frflow.Lifted((s: frflow.fixtures.Shelf) => s match { case b: frflow.fixtures.Shelf.Box => 1; case _ => 2 })")
      .contains("type test"))
  }

  test("a local name may not shadow a parameter, which is a Lean variable of the same name") {
    assert(compileErrors("frflow.Lifted((minPages: Int) => minPages > frflow.fixtures.minPages.value)")
      .contains("names both a parameter"))
  }

  test("calls of defined functions are marked for the generator") {
    val c = Lifted((b: Book) => long(b))
    assertEquals(c.body, "(⟦long⟧ b)")
    assertEquals(c.defs.map(_.name), List("long"))
    assertEquals(long.name, "long")
  }

  test("specification logic") {
    val c = Lifted((l: List[Book]) => forall((a: Book, b: Book) => (l.contains(a) && l.contains(b)) ==> a.pages <= b.pages))
    assertEquals(c.body, "(∀ (a : Book) (b : Book), (((a ∈ l) ∧ (b ∈ l)) → (a.pages ≤ b.pages)))")
    val o = Lifted((o: Option[Book]) => o.forall(b => b.pages > 0))
    assertEquals(o.body, "(∀ b, o = some b → (b.pages > 0))")
  }

  test("unsupported Scala is a compile error") {
    assert(compileErrors("frflow.Lifted((x: Int) => { var y = x; y })").contains("FrFlow: `var` is not supported"))
    assert(compileErrors("frflow.Lifted((x: Int) => println(x))").contains("FrFlow:"))
  }
