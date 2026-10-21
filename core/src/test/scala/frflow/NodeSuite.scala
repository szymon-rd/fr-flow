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
    assert(compileErrors("""frflow.fixtures.onlyGood.contract[Int, Int, Int]("C", "c", "w")((a, b, r) => true)""").nonEmpty)
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

  test("examples are checked against the contract and the registered implementation") {
    val rs = shelfKb.exampleResults(pick)
    assertEquals(rs.map(r => (r.contract, r.implementation)), List(("ok", Some("ok")), ("ok", Some("ok")), ("ok", Some("ok"))))
    // a useless implementation: proven contract, but it does not do what was decided
    val lazyKb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick).implement(pick)((_, _) => Nil)
    assertEquals(lazyKb.exampleResults(pick).head.implementation, Some("returned List()"))
    // a contract that refuses what was decided
    val strict = books.contract[List[Book], Int, List[Book]]("Strict", "Nothing is picked.", "w")((_, _, picked) => picked.isEmpty)
      .examples(minPages.bind(100))(expect(List(Book("Long", 300)), 1, List(Book("Long", 300)), "the long book"))
    assertEquals(strict.checkExamples(None).head.contract, "the contract refuses it")
  }

  test("every node says why; several roots are allowed; generated names are reserved") {
    val noWhy = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("NoWhy", "s", " ")(abs = p => p, spec = p => true)
    assert(KnowledgeBase("K", "IDEA.md")(onlyGood, noWhy).problems.exists(_.contains("say why")))
    val other = Node.root[Int => Int]("Other", "s", "w")(f => true)
    assertEquals(KnowledgeBase("K", "IDEA.md")(onlyGood, other).problems, Nil)
    val m = Param[Int]("m", "a bound")
    val clash = Node.root[Int => Int]("Clash", "s", "w")(f => forall((x: Int) => f(x) >= m.value))
    assert(KnowledgeBase("K", "IDEA.md")(clash).problems.exists(_.contains("reserved")))
  }

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

  test("proof files may contain only tactic proofs") {
    val ok = Generate(squareKb).proofFile(squares).replace("sorry", "simp")
    assertEquals(Lean.violations(ok), Nil)
    val bad = "import Lean\nrun_cmd do pure ()\nset_option debug.skipKernelTC true\nattribute [simp] foo\n#eval 1\ntheorem link : Obl.link := by simp\n"
    assertEquals(Lean.violations(bad).map(_._2).toSet,
      Set("import", "command run_cmd", "metaprogram", "set_option", "command attribute", "attribute", "command #eval"))
    assert(Lean.violations("set_option\n  debug.skipKernelTC true\n").nonEmpty)
  }

  test("domain types keep structural equality, even through a trait") {
    val errs = compileErrors("""
      trait CaseInsensitive { override def equals(o: Any): Boolean = true; override def hashCode: Int = 0 }
      final case class PathCI(v: String) extends CaseInsensitive
      frflow.Lifted((p: PathCI, q: PathCI) => p == q)
    """)
    assert(errs.contains("structural equality"), errs)
  }

  test("a contract's examples must tell a constant implementation apart") {
    val lazyPick = books.contract[List[Book], Int, List[Book]]("LazyPick", "s", "w")((_, _, picked) => picked.isEmpty)
      .examples(minPages.bind(100))(expect(Nil, 1, Nil, "nothing"), reject(List(Book("L", 300)), 1, List(Book("L", 300)), "x"))
    assert(KnowledgeBase("K", "IDEA.md")(onlyGood, listed, books, lazyPick).problems.exists(_.contains("always returns it")))
  }
