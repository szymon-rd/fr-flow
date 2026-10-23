package frflow

import frflow.fixtures.*

/** Terms: written in Scala, printed as the Lean the macro printed for the same Scala, and run as Scala. */
class TermSuite extends munit.FunSuite:
  private val four = Param[(Book, Int, Int, String) => Boolean]("four", "a test of four arguments")

  private def lifted1[A, R](f: Term[A] => Term[R])(using a: LeanType[A]): Lifted[A => R] = Lifted.lambda(f, List(a), "")
  private def lifted2[A, B, R](f: (Term[A], Term[B]) => Term[R])(using a: LeanType[A], b: LeanType[B]): Lifted[(A, B) => R] =
    Lifted.lambda(f, List(a, b), "")
  private def lean1[A, R](f: Term[A] => Term[R])(using LeanType[A]): String = lifted1(f).body
  private def lean2[A, B, R](f: (Term[A], Term[B]) => Term[R])(using LeanType[A], LeanType[B]): String = lifted2(f).body

  test("terms print as the Lean the macro printed") {
    List(
      // case classes: construction, fields, copy
      lean1((b: Term[Book]) => b.copy((pages = 2)) === Book(b.title, b.pages)) -> "({ b with pages := 2 } = (Book.mk b.title b.pages))",
      // enums and match
      where.lifted.body -> "(match s with | Shelf.Top => \"top\" | Shelf.Bottom => \"bottom\" | Shelf.Box l => l)",
      // opaque types and parameters are Lean variables; defined functions are marked for the generator
      lean1((x: Term[Item.T]) => good(x)) -> "(good x)",
      lean1((b: Term[Book]) => long(b)) -> "(⟦long⟧ b)",
      lean1((b: Term[Book]) => pagesBetween(b, 1, 500, "x")) -> "(⟦pagesBetween⟧ b 1 500 \"x\")",
      lean1((b: Term[Book]) => pagesBetweenOn(b, 1, 500, "x", Shelf.Top)) -> "(⟦pagesBetweenOn⟧ b 1 500 \"x\" Shelf.Top)",
      lean1((b: Term[Book]) => four(b, 1, 2, "x")) -> "(four b 1 2 \"x\")",
      // tuples nest as Lean's: A × B × C is A × (B × C)
      lean1((t: Term[(BigInt, BigInt, BigInt)]) => t._2 * 10 + t._3) -> "((t.2.1 * 10) + t.2.2)",
      lean1((t: Term[(BigInt, BigInt)]) => t._1 - t._2) -> "(t.1 - t.2)",
      // a list's elements as a set: its membership
      lean2((l: Term[List[Book]], b: Term[Book]) => l.toSet.contains(b)) -> "((fun y => y ∈ l) b)",
      keptOnce.lifted.body -> "(let there : (Book → Prop) := (fun y => y ∈ shelf); (List.filter (fun b => decide (there b)) picked))",
      // specification logic, and the quantifier forms of roots
      lean1((l: Term[List[Book]]) => forall((a: Term[Book], b: Term[Book]) => (l.contains(a) && l.contains(b)) ==> a.pages <= b.pages)) ->
        "(∀ (a : Book) (b : Book), (((a ∈ l) ∧ (b ∈ l)) → (a.pages ≤ b.pages)))",
      lean1((o: Term[Option[Book]]) => o.forall(b => b.pages > 0)) -> "(∀ b, o = some b → (b.pages > 0))",
      lean1((f: Term[(BigInt, BigInt) => Boolean]) => forall((x: Term[BigInt], y: Term[BigInt]) => forall((z: Term[BigInt]) => f(x, z) ==> f(y, z)))) ->
        "(∀ (x : Int) (y : Int), (∀ (z : Int), ((f x z) → (f y z))))",
      lean1((name: Term[String]) => exists((s: Term[Shelf]) => where(s) === name)) -> "(∃ (s : Shelf), ((⟦«where»⟧ s) = name))",
      lean1((xs: Term[List[Book]]) => xs.forall(b => xs.exists(c => c.title === b.title && c.pages >= b.pages))) ->
        "(∀ b ∈ xs, (∃ c ∈ xs, ((c.title = b.title) ∧ (c.pages ≥ b.pages))))",
      lean1((a: Term[BigInt]) => exists((c: Term[BigInt]) => c > a)) -> "(∃ (c : Int), (c > a))",
      // exact arithmetic
      lean1((x: Term[BigInt]) => x + 1 > x) -> "((x + 1) > x)",
      lean1((x: Term[BigInt]) => x / 2) -> "(Int.tdiv x 2)",
      lean1((l: Term[List[BigInt]]) => l.foldLeft(BigInt(0): Term[BigInt])((acc, x) => acc + x) >= 0) -> "((List.foldl (fun (acc : Int) (x : Int) => (acc + x)) 0 l) ≥ 0)",
      // no binder captures another variable, whatever the Scala names
      lean2((l: Term[List[Book]], x_1: Term[Book]) => l.forall(x => x === x_1)) -> "(∀ x ∈ l, (x = x_1))",
      lean1((l: Term[List[Book]]) => l.forall(b => b.pages > 0) && l.exists(b => b.pages > 1)) ->
        "((∀ b ∈ l, (b.pages > 0)) ∧ (∃ b_1 ∈ l, (b_1.pages > 1)))",
      // names Lean defines are not captured
      lean1((some: Term[Int]) => some > 1) -> "(some_ > 1)",
      // matches on an Option, with a wildcard
      lean1((o: Term[Option[Book]]) => o.on[Some[Book]](b => b.pages).on[None.type](0)) -> "(match o with | some b => b.pages | none => 0)",
      lean1((s: Term[Shelf]) => s.on[Shelf.Box](_ => True).on[Shelf.Top.type](False).on[Shelf.Bottom.type](False)) ->
        "(match s with | Shelf.Box _ => True | Shelf.Top => False | Shelf.Bottom => False)",
      lean1((b: Term[Book]) => If(b.pages > 1)(b.title).Else("none")) -> "(if (b.pages > 1) then b.title else \"none\")"
    ).foreach((got, want) => assertEquals(got, want))
    val d = lean2((l: Term[List[Book]], x: Term[Book]) => l.forall(x_1 => l.exists(x => x === x_1)))
    assert(!d.contains("(x = x)") && !d.contains("(x_1 = x_1)"), d)
    // calls hidden in strings stay strings
    assert(lean1((s: Term[String]) => s === "⟦long⟧").contains("\\u27E6long\\u27E7"))
    val m = lean2((m: Term[Map[String, BigInt]], k: Term[String]) => m.updated(k, BigInt(1)).get(k) === Some(BigInt(1)) && !m.removed(k).contains(k))
    assert(m.contains("then some 1 else m"), m)
    val ls = lean2((l: Term[List[BigInt]], n: Term[Int]) =>
      l.flatMap(x => List(x, x)).take(n).drop(1).headOption === l.find(x => x > 0) && l.zip(l).filterNot(p => p._1 > p._2).nonEmpty)
    assert(List("List.flatMap", "List.take (Int.toNat n)", "List.find?", "List.zip l l").forall(ls.contains), ls)
    // values print as the macro printed them written in Scala
    assertEquals(lean1((o: Term[Option[Book]]) => o === Some(Book("A", -1))), "(o = (some (Book.mk \"A\" (-1))))")
    assertEquals(lean1((s: Term[Shelf]) => s === Shelf.Box("x") || s === Shelf.Top), "((s = (Shelf.Box \"x\")) ∨ (s = Shelf.Top))")
    // an enum's case built from terms, through its companion
    assertEquals(lean1((l: Term[String]) => Shelf[Shelf.Box](l) =!= Shelf.Top), "((Shelf.Box l) ≠ Shelf.Top)")
    assertEquals(lifted1((l: Term[String]) => Shelf[Shelf.Box](l)).value("x"), Shelf.Box("x"))
  }

  test("what a term mentions: its parameters, types, opaque types and defined functions") {
    val c = lifted1((x: Term[Item.T]) => good(x))
    assertEquals((c.params, c.opaques, c.paramRefs, c.paramObjects.map(_.name)), (List("x" -> "Item"), List("Item"), List("good" -> "(Item → Prop)"), List("good")))
    assertEquals(lifted1((b: Term[Book]) => long(b)).defs.map(_.name), List("long"))
    assertEquals(long.name, "long")
    assert(lifted1((b: Term[Book]) => b.pages > 0).types.exists(t => t.name == "Book" && t.lean.contains("pages : Int")))
    assert(where.lifted.types.exists(_.lean.contains("| Box (label : String)")))
    val m = lifted2((m: Term[Map[String, BigInt]], k: Term[String]) => m.get(k) === Some(BigInt(1)))
    assertEquals(m.params, List("m" -> "(String → Option Int)", "k" -> "String"))
    assertEquals(lifted2((xs: Term[Set[String]], x: Term[String]) => (xs + x).contains(x)).params.head, "xs" -> "(String → Prop)")
    // a claim's formula reads as written
    assertEquals(onlyGood.formula.map(f => (f.source, f.params)),
      Some(("forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) === (l.contains(x) && good(x)))", Nil)))
  }

  test("a term also runs as Scala") {
    val c = lifted1((b: Term[Book]) => b.copy((pages = 2)) === Book(b.title, b.pages))
    assert(c.value(Book("x", 2)) && !c.value(Book("x", 5)))
    assert(lifted2((m: Term[Map[String, BigInt]], k: Term[String]) => m.updated(k, BigInt(1)).get(k) === Some(BigInt(1)) && !m.removed(k).contains(k))
      .value(Map("a" -> BigInt(2)), "a"))
    assertEquals(where.fn(Shelf.Box("b")), "b")
    assertEquals(where.fn(Shelf.Top), "top")
    assertEquals((pagesBetween.fn(Book("A", 300), 100, 500, "B"), pagesBetweenOn.fn(Book("A", 300), 100, 500, "top", Shelf.Top)), (true, false))
    assertEquals(keptOnce.fn(List(Book("A", 1)), List(Book("A", 1), Book("B", 2))), List(Book("A", 1)))
    assertEquals(lifted1((l: Term[List[BigInt]]) => l.foldLeft(BigInt(0): Term[BigInt])((acc, x) => acc + x)).value(List(BigInt(2), BigInt(3))), BigInt(5))
    intercept[NotExecutable](lifted1((a: Term[BigInt]) => exists((c: Term[BigInt]) => c > a)).value(BigInt(1)))
  }

  test("what would mean something else in Lean is refused, saying why") {
    def refused(l: => Lifted[?], says: String): Unit =
      val e = intercept[IllegalArgumentException](l.body)
      assert(e.getMessage.contains(says), e.getMessage)
    // nothing is said to exist of a bounded integer, which Lean's unbounded Int would find
    refused(lifted1((a: Term[Long]) => exists((c: Term[Long]) => c > a)), "unbounded")
    refused(lifted1((b: Term[Book]) => exists((c: Term[Book]) => c.pages > b.pages)), "unbounded")
    refused(lifted1((b: Term[Book]) => !forall((c: Term[Book]) => c.pages > b.pages)), "negated forall")
    // a local name may not shadow a parameter, which is a Lean variable of the same name
    refused(lifted1((minPages: Term[Int]) => minPages > fixtures.minPages), "names both a parameter")
    intercept[IllegalArgumentException](Param[BigInt]("z", "a number") / 0)
    // and what Scala would compute otherwise does not compile
    List(
      compileErrors("(m: frflow.Term[Map[String, BigInt]], k: frflow.Term[String]) => m(k)"),
      compileErrors("(x: frflow.Term[Int]) => x + 1"),
      compileErrors("(x: frflow.Term[BigInt], y: frflow.Term[BigInt]) => x / y")
    ).foreach(errors => assert(errors.nonEmpty))
    assert(compileErrors("(x: frflow.Term[BigInt]) => x == x").contains("compare terms with ==="))
  }
