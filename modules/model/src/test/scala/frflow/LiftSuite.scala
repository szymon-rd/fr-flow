package frflow

import frflow.fixtures.*

/** The macro: Scala in, Lean out, with the Scala still executable. */
class LiftSuite extends munit.FunSuite:
  private val four = Param[(Book, Int, Int, String) => Boolean]("four", "a test of four arguments")

  test("Scala terms translate to Lean terms") {
    List(
      // case classes: construction, fields, copy
      Lifted((b: Book) => b.copy(pages = 2) == Book(b.title, b.pages)).body -> "({ b with pages := 2 } = (Book.mk b.title b.pages))",
      // enums and match
      where.lifted.body -> "(match s with | Shelf.Top => \"top\" | Shelf.Bottom => \"bottom\" | Shelf.Box l => l)",
      // opaque types and parameters are Lean variables; defined functions are marked for the generator
      Lifted((x: Item.T) => good(x)).body -> "(good x)",
      Lifted((b: Book) => long(b)).body -> "(⟦long⟧ b)",
      Lifted((b: Book) => pagesBetween(b, 1, 500, "x")).body -> "(⟦pagesBetween⟧ b 1 500 \"x\")",
      Lifted((b: Book) => pagesBetweenOn(b, 1, 500, "x", Shelf.Top)).body -> "(⟦pagesBetweenOn⟧ b 1 500 \"x\" Shelf.Top)",
      Lifted((b: Book) => four(b, 1, 2, "x")).body -> "(four b 1 2 \"x\")",
      // tuples nest as Lean's: A × B × C is A × (B × C)
      Lifted((t: (BigInt, BigInt, BigInt)) => t._2 * 10 + t._3).body -> "((t.2.1 * 10) + t.2.2)",
      Lifted((t: (BigInt, BigInt)) => t._1 - t._2).body -> "(t.1 - t.2)",
      // a list's elements as a set: its membership
      Lifted((l: List[Book], b: Book) => l.toSet.contains(b)).body -> "((fun y => y ∈ l) b)",
      keptOnce.lifted.body -> "(let there : (Book → Prop) := (fun y => y ∈ shelf); (List.filter (fun b => decide (there b)) picked))",
      // specification logic, and the quantifier forms of roots (no example checks their translation)
      Lifted((l: List[Book]) => forall((a: Book, b: Book) => (l.contains(a) && l.contains(b)) ==> a.pages <= b.pages)).body ->
        "(∀ (a : Book) (b : Book), (((a ∈ l) ∧ (b ∈ l)) → (a.pages ≤ b.pages)))",
      Lifted((o: Option[Book]) => o.forall(b => b.pages > 0)).body -> "(∀ b, o = some b → (b.pages > 0))",
      Lifted((f: (BigInt, BigInt) => Boolean) => forall((x: BigInt, y: BigInt) => forall((z: BigInt) => f(x, z) ==> f(y, z)))).body ->
        "(∀ (x : Int) (y : Int), (∀ (z : Int), ((f x z) → (f y z))))",
      Lifted((name: String) => exists((s: Shelf) => where(s) == name)).body -> "(∃ (s : Shelf), ((⟦«where»⟧ s) = name))",
      Lifted((xs: List[Book]) => xs.forall(b => xs.exists(c => c.title == b.title && c.pages >= b.pages))).body ->
        "(∀ b ∈ xs, (∃ c ∈ xs, ((c.title = b.title) ∧ (c.pages ≥ b.pages))))",
      Lifted((a: BigInt) => frflow.exists((c: BigInt) => c > a)).body -> "(∃ (c : Int), (c > a))",
      // exact arithmetic
      Lifted((x: BigInt) => x + 1 > x).body -> "((x + 1) > x)",
      Lifted((x: BigInt) => x / 2).body -> "(Int.tdiv x 2)",
      Lifted((l: List[BigInt]) => l.foldLeft(BigInt(0))((acc, x) => acc + x) >= 0).body -> "((List.foldl (fun (acc : Int) (x : Int) => (acc + x)) 0 l) ≥ 0)",
      // no binder captures another variable, whatever the Scala names
      Lifted((l: List[Book], x_1: Book) => l.forall(x => x == x_1)).body -> "(∀ x ∈ l, (x = x_1))",
      Lifted((l: List[Book]) => l.forall(b => b.pages > 0) && l.exists(b => b.pages > 1)).body ->
        "((∀ b ∈ l, (b.pages > 0)) ∧ (∃ b_1 ∈ l, (b_1.pages > 1)))",
      // names Lean defines are not captured
      Lifted((some: Int) => some > 1).body -> "(some_ > 1)"
    ).foreach((got, want) => assertEquals(got, want))
    val d = Lifted((l: List[Book], x: Book) => l.forall(x_1 => l.exists(x => x == x_1)))
    assert(!d.body.contains("(x = x)") && !d.body.contains("(x_1 = x_1)"), d.body)
    // calls hidden in strings stay strings
    assert(Lifted((s: String) => s == "⟦long⟧").body.contains("\\u27E6long\\u27E7"))
    val m = Lifted((m: Map[String, BigInt], k: String) => m.updated(k, BigInt(1)).get(k) == Some(BigInt(1)) && !m.removed(k).contains(k))
    assert(m.body.contains("then some 1 else m"), m.body)
    val ls = Lifted((l: List[BigInt], n: Int) =>
      l.flatMap(x => List(x, x)).take(n).drop(1).headOption == l.find(x => x > 0) && l.zip(l).filterNot(p => p._1 > p._2).nonEmpty)
    assert(List("List.flatMap", "List.take (Int.toNat n)", "List.find?", "List.zip l l").forall(ls.body.contains), ls.body)
  }

  test("what a translation mentions: its parameters, types, opaque types and defined functions") {
    val c = Lifted((x: Item.T) => good(x))
    assertEquals((c.params, c.opaques, c.paramRefs, c.paramObjects.map(_.name)), (List("x" -> "Item"), List("Item"), List("good" -> "(Item → Prop)"), List("good")))
    assertEquals(Lifted((b: Book) => long(b)).defs.map(_.name), List("long"))
    assertEquals(long.name, "long")
    assert(Lifted((b: Book) => b.pages > 0).types.exists(t => t.name == "Book" && t.lean.contains("pages : Int")))
    assert(where.lifted.types.exists(_.lean.contains("| Box (label : String)")))
    val m = Lifted((m: Map[String, BigInt], k: String) => m.get(k) == Some(BigInt(1)))
    assertEquals(m.params, List("m" -> "(String → Option Int)", "k" -> "String"))
    assertEquals(Lifted((xs: Set[String], x: String) => (xs + x).contains(x)).params.head, "xs" -> "(String → Prop)")
    // a claim's formula reads as written, not as the lambda that wraps it
    assertEquals(onlyGood.formula.map(f => (f.source, f.params)), Some(("forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good(x)))", Nil)))
  }

  test("the Scala of a translation still runs") {
    val c = Lifted((b: Book) => b.copy(pages = 2) == Book(b.title, b.pages))
    assert(c.value(Book("x", 2)) && !c.value(Book("x", 5)))
    assert(Lifted((m: Map[String, BigInt], k: String) => m.updated(k, BigInt(1)).get(k) == Some(BigInt(1)) && !m.removed(k).contains(k)).value(Map("a" -> BigInt(2)), "a"))
    assertEquals(where(Shelf.Box("b")), "b")
    assertEquals((pagesBetween(Book("A", 300), 100, 500, "B"), pagesBetweenOn(Book("A", 300), 100, 500, "top", Shelf.Top)), (true, false))
    assertEquals(keptOnce(List(Book("A", 1)), List(Book("A", 1), Book("B", 2))), List(Book("A", 1)))
  }

  test("Scala outside the subset, or meaning something else in Lean, is a compile error saying why") {
    List(
      compileErrors("frflow.Lifted((m: Map[String, BigInt], k: String) => m(k) > 0)") -> "m(k) throws",
      // nothing is said to exist of a bounded integer, which Lean's unbounded Int would find
      compileErrors("frflow.Lifted((a: Long) => frflow.exists((c: Long) => c > a))") -> "unbounded",
      compileErrors("frflow.Lifted((b: frflow.fixtures.Book) => frflow.exists((c: frflow.fixtures.Book) => c.pages > b.pages))") -> "unbounded",
      // patterns Lean would read as catch-alls
      compileErrors("frflow.Lifted((o: Option[Boolean]) => o match { case Some(true) => 1; case _ => 2 })") -> "matching on true or false",
      compileErrors("frflow.Lifted((s: frflow.fixtures.Shelf) => s match { case b: frflow.fixtures.Shelf.Box => 1; case _ => 2 })") -> "type test",
      // a local name may not shadow a parameter, which is a Lean variable of the same name
      compileErrors("frflow.Lifted((minPages: Int) => minPages > frflow.fixtures.minPages.value)") -> "names both a parameter",
      compileErrors("frflow.Lifted((x: Int) => x + 1 > x)") -> "can overflow in Scala",
      compileErrors("frflow.Lifted((x: Long) => x * 2)") -> "can overflow in Scala",
      compileErrors("frflow.Lifted((x: BigInt, y: BigInt) => x / y)") -> "may be zero",
      compileErrors("frflow.Lifted((x: Int) => { var y = x; y })") -> "FrFlow: `var` is not supported",
      compileErrors("frflow.Lifted((x: Int) => println(x))") -> "FrFlow:",
      // with the usual rewrite, for what is often written outside the subset
      compileErrors("frflow.Lifted((xs: List[BigInt]) => xs.count(x => x > 0))") -> "xs.filter(p).length",
      compileErrors("frflow.Lifted((xs: List[BigInt]) => xs.sum)") -> "foldLeft",
      compileErrors("frflow.Lifted((o: Option[BigInt]) => o.toList)") -> "match on it"
    ).foreach((errors, says) => assert(errors.contains(says), errors))
  }
