package frflow

import frflow.fixtures.*

/** The macro: Scala in, Lean out, with the Scala still executable. */
class LiftSuite extends munit.FunSuite:

  test("case classes: construction, fields, copy") {
    val c = Lifted((b: Book) => b.copy(pages = 2) == Book(b.title, b.pages))
    assertEquals(c.body, "({ b with pages := 2 } = (Book.mk b.title b.pages))")
    assertEquals(c.params, List("b" -> "Book"))
    assert(c.types.exists(t => t.name == "Book" && t.lean.contains("pages : Int")))
    assert(c.value(Book("x", 2)))
    assert(!c.value(Book("x", 5)))
  }

  test("maps and sets are functions: a map from keys to what each is bound to, a set its membership") {
    val c = Lifted((m: Map[String, BigInt], k: String) => m.updated(k, BigInt(1)).get(k) == Some(BigInt(1)) && !m.removed(k).contains(k))
    assertEquals(c.params, List("m" -> "(String → Option Int)", "k" -> "String"))
    assert(c.body.contains("if k_1 = k then some 1 else m k_1") || c.body.contains("then some 1 else m"), c.body)
    assert(c.value(Map("a" -> BigInt(2)), "a"))
    val s = Lifted((xs: Set[String], x: String) => (xs + x).contains(x) && xs.subsetOf(xs ++ Set(x)))
    assertEquals(s.params.head, "xs" -> "(String → Prop)")
    assert(s.value(Set("a"), "b"))
    assert(compileErrors("frflow.Lifted((m: Map[String, BigInt], k: String) => m(k) > 0)").contains("m(k) throws"))
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

  test("no binder captures another variable, whatever the Scala names") {
    // `x` inside would become `x_1` if names were made fresh only against the receiver: `x_1 = x_1`.
    val c = Lifted((l: List[Book], x_1: Book) => l.forall(x => x == x_1))
    assertEquals(c.body, "(∀ x ∈ l, (x = x_1))")
    val d = Lifted((l: List[Book], x: Book) => l.forall(x_1 => l.exists(x => x == x_1)))
    assert(!d.body.contains("(x = x)") && !d.body.contains("(x_1 = x_1)"), d.body)
    // the same name in two scopes: two Lean names
    val e = Lifted((l: List[Book]) => l.forall(b => b.pages > 0) && l.exists(b => b.pages > 1))
    assertEquals(e.body, "((∀ b ∈ l, (b.pages > 0)) ∧ (∃ b_1 ∈ l, (b_1.pages > 1)))")
  }

  test("nothing is said to exist of a bounded integer, which Lean's unbounded Int would find") {
    assert(compileErrors("frflow.Lifted((a: Long) => frflow.exists((c: Long) => c > a))").contains("unbounded"))
    assert(compileErrors("frflow.Lifted((b: frflow.fixtures.Book) => frflow.exists((c: frflow.fixtures.Book) => c.pages > b.pages))").contains("unbounded"))
    // over BigInt it is what it says
    assert(Lifted((a: BigInt) => frflow.exists((c: BigInt) => c > a)).body.contains("∃"))
  }

  test("tuple fields follow Lean's nesting: A × B × C is A × (B × C)") {
    val c = Lifted((t: (BigInt, BigInt, BigInt)) => t._2 * 10 + t._3)
    assertEquals(c.body, "((t.2.1 * 10) + t.2.2)")
    assertEquals(c.value((1, 2, 3)), BigInt(23))
    assertEquals(Lifted((t: (BigInt, BigInt)) => t._1 - t._2).body, "(t.1 - t.2)")
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

  test("defined functions of four and five arguments are called, in Scala and in Lean") {
    assertEquals(Lifted((b: Book) => pagesBetween(b, 1, 500, "x")).body, "(⟦pagesBetween⟧ b 1 500 \"x\")")
    assertEquals(Lifted((b: Book) => pagesBetweenOn(b, 1, 500, "x", Shelf.Top)).body, "(⟦pagesBetweenOn⟧ b 1 500 \"x\" Shelf.Top)")
    assertEquals(pagesBetween(Book("A", 300), 100, 500, "B"), true)
    assertEquals(pagesBetweenOn(Book("A", 300), 100, 500, "top", Shelf.Top), false)
    val four = Param[(Book, Int, Int, String) => Boolean]("four", "a test of four arguments")
    assertEquals(Lifted((b: Book) => four(b, 1, 2, "x")).body, "(four b 1 2 \"x\")")
  }

  test("specification logic") {
    val c = Lifted((l: List[Book]) => forall((a: Book, b: Book) => (l.contains(a) && l.contains(b)) ==> a.pages <= b.pages))
    assertEquals(c.body, "(∀ (a : Book) (b : Book), (((a ∈ l) ∧ (b ∈ l)) → (a.pages ≤ b.pages)))")
    val o = Lifted((o: Option[Book]) => o.forall(b => b.pages > 0))
    assertEquals(o.body, "(∀ b, o = some b → (b.pages > 0))")
  }

  test("arithmetic is exact in Lean and in Scala: BigInt, and division only by a literal") {
    assert(compileErrors("frflow.Lifted((x: Int) => x + 1 > x)").contains("can overflow in Scala"))
    assert(compileErrors("frflow.Lifted((x: Long) => x * 2)").contains("can overflow in Scala"))
    assertEquals(Lifted((x: BigInt) => x + 1 > x).body, "((x + 1) > x)")
    assertEquals(Lifted((x: BigInt) => x / 2).body, "(Int.tdiv x 2)")
    assert(compileErrors("frflow.Lifted((x: BigInt, y: BigInt) => x / y)").contains("may be zero"))
  }

  test("lists: flatMap, find, headOption, take and drop, zip, filterNot") {
    val c = Lifted((l: List[BigInt], n: Int) =>
      l.flatMap(x => List(x, x)).take(n).drop(1).headOption == l.find(x => x > 0) && l.zip(l).filterNot(p => p._1 > p._2).nonEmpty)
    assert(c.body.contains("List.flatMap") && c.body.contains("List.take (Int.toNat n)") && c.body.contains("List.find?") && c.body.contains("List.zip l l"), c.body)
    assert(c.value(List(BigInt(1), BigInt(2)), 3))
  }

  test("a fold over a list: what a sequence of steps leads to") {
    val c = Lifted((l: List[BigInt]) => l.foldLeft(BigInt(0))((acc, x) => acc + x) >= 0)
    assertEquals(c.body, "((List.foldl (fun (acc : Int) (x : Int) => (acc + x)) 0 l) ≥ 0)")
    assert(c.value(List(BigInt(1), BigInt(2))))
  }

  test("names Lean defines cannot be captured, nor calls hidden in strings") {
    assertEquals(Lifted((some: Int) => some > 1).body, "(some_ > 1)")
    assert(Lifted((s: String) => s == "⟦long⟧").body.contains("\\u27E6long\\u27E7"))
  }

  test("unsupported Scala is a compile error") {
    assert(compileErrors("frflow.Lifted((x: Int) => { var y = x; y })").contains("FrFlow: `var` is not supported"))
    assert(compileErrors("frflow.Lifted((x: Int) => println(x))").contains("FrFlow:"))
  }

  // Roots and refinements are not run, so no example or probe checks their translation: their forms are pinned here.
  test("the quantifier forms of roots: nested binders, an implication inside, an existential over a case class") {
    val nested = Lifted((f: (BigInt, BigInt) => Boolean) => forall((x: BigInt, y: BigInt) => forall((z: BigInt) => f(x, z) ==> f(y, z))))
    assertEquals(nested.body, "(∀ (x : Int) (y : Int), (∀ (z : Int), ((f x z) → (f y z))))")
    val ex = Lifted((name: String) => exists((s: Shelf) => where(s) == name))
    assertEquals(ex.body, "(∃ (s : Shelf), ((⟦«where»⟧ s) = name))")
    val inList = Lifted((xs: List[Book]) => xs.forall(b => xs.exists(c => c.title == b.title && c.pages >= b.pages)))
    assertEquals(inList.body, "(∀ b ∈ xs, (∃ c ∈ xs, ((c.title = b.title) ∧ (c.pages ≥ b.pages))))")
  }

  test("a claim's formula reads as written, not as the lambda that wraps it") {
    assertEquals(onlyGood.formula.get.source, "forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good(x)))")
    assertEquals(onlyGood.formula.get.params, Nil)
  }
