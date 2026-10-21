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
