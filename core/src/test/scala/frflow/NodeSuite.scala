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

  test("the implementation is also run on combinations of the examples' inputs") {
    val two = books.contract[List[Book], Int, List[Book]]("Two", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
    // passes every example, but returns the whole shelf when asked for one book from several
    val kb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, two)
      .implement(two)((s, n) => if s.size > 1 && n == 1 then s else s.filter(_.pages >= minPages.value).take(n))
    val rs = kb.exampleResults(two)
    assertEquals(rs.take(3).flatMap(_.implementation), List("ok", "ok", "ok"))
    val generated = rs.drop(3)
    // the combination (shelf of two, one book), and calls varied from the examples
    assert(generated.exists(r => r.example.note.startsWith("generated from the examples' inputs")), generated)
    assert(generated.forall(_.implementation.exists(_.contains("breaks the contract"))), generated)
  }

  test("a spec condition that does not mention the model is shown as an assumption about the world") {
    val assumed = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Assumed", "s", "w")(
      abs = pick => pick, spec = pick => forall((x: Item.T) => good(x)) && forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x))))
    val kb = KnowledgeBase("A", idea = "IDEA.md")(onlyGood, assumed)
    assertEquals(kb.limits(assumed).size, 1, kb.limits(assumed))
    assert(kb.limits(assumed).head.contains("assumes about the world"))
    assertEquals(kb.limits(listed), Nil)
  }

  test("a cross-cutting invariant is kept by the contracts that name it, on examples, generated calls and at run time") {
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "Readers carry what they asked for.")(
      (asked, picked) => picked <= asked)
    val kept = books.contract[List[Book], Int, List[Book]]("Kept", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
    val kb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, kept, atMostN)
      .implement(kept)((s, n) => s.filter(_.pages >= minPages.value).take(n))
    assertEquals(kb.problems, Nil)
    assert(kb.exampleResults(kept).forall(_.implementation.contains("ok")), kb.exampleResults(kept))
    // every long book, twice: meets the post, breaks the invariant when one is asked for
    val bad = kb.implement(kept)((s, n) => s.filter(_.pages >= minPages.value) ++ s.filter(_.pages >= minPages.value))
    assert(bad.exampleResults(kept).flatMap(_.implementation).exists(_.contains("breaks the invariant AtMostN")), bad.exampleResults(kept))
    val run = bad.service(kept)(minPages.bind(100))
    intercept[ContractViolation](run(List(Book("Long", 300)), 1))
    // every contract in its scope keeps it or says why not; an invariant nobody keeps is a problem
    // every contract whose result can hold what the rule is about keeps it or says why not
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b))
    val unkept = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick, fromShelf).problems
    assert(unkept.exists(_.contains("no contract keeps")), unkept)
    assert(unkept.exists(_.startsWith("Pick: keep FromShelf")), unkept)
    val exempt = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books,
      pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b))), kept.exempt(fromShelf, "the shelf is checked by Pick"), fromShelf, atMostN)
    assertEquals(exempt.problems, Nil)
    // a rule about numbers does not reach a contract that returns books
    assert(!KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick, kept, atMostN).problems.exists(_.startsWith("Pick: keep AtMostN")))
    // an invariant scoped to another subtree does not apply
    val scoped = Node.invariant[List[Book], Book]("Scoped", "s", "w", scope = List(onlyGood))((shelf, b) => shelf.contains(b))
    assert(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick, scoped).problems.exists(_.startsWith("Pick: keep Scoped")))
  }

  test("two different parameters with one name are a problem") {
    val other = Param[Int]("minPages", "the pages a reader can carry")
    val c = books.contract[List[Book], Int, List[Book]]("Clash", "s", "w")((shelf, n, picked) => picked.length <= other.value)
    val ps = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, c).problems
    assert(ps.exists(_.startsWith("two different parameters are named minPages")), ps)
  }

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
