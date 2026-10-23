package frflow

import frflow.fixtures.*

/** Nodes, the structure of the DAG, and enforcement, on the shelf fixture. */
class NodeSuite extends munit.FunSuite:

  test("the knowledge base is well formed: one root, parts under it, definitions beside") {
    assertEquals(shelfKb.problems, Nil)
    assertEquals(shelfKb.root.map(_.id), Some("OnlyGood"))
    // every node after what it rests on: the definitions it uses, its parents
    val order = shelfKb.ordered.map(_.id)
    assertEquals(order, List("Books", "Picking", "OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    assertEquals(shelfKb.params.map(_.name), List("good", "minPages", "picks", "shown"))
    assertEquals(shelfKb.definitions.map(_.id), List("Books", "Picking"))
  }

  test("a contract's post has its operation's type") {
    assert(compileErrors("""frflow.Node.contract(frflow.fixtures.picks)("C", "c", "w")((a: Int, b: Int, r: Int) => true)""").nonEmpty)
  }

  test("structure: one root, no cycles, a part under the nodes it proves, a design under what it serves") {
    val other = Node.claim("Other", "s", "w")(forall((x: BigInt) => sq(x) >= 0))
    assert(shelfWith(pick, other).problems.exists(_.message.startsWith("one root only")), shelfWith(pick, other).problems)
    assert(KnowledgeBase("K", "IDEA.md")(fromList).problems.exists(_.message.contains("a root is required")))
    // a contract no code calls and nothing is above
    assert(shelfWith(pick, pickPromise).problems.exists(_.message.startsWith("PickPromise has no parents")))
    val loose = Node.design("Loose", "Shelves are cached.", "They change once a day.")()
    assert(shelfWith(pick, loose).problems.exists(_.message.startsWith("Loose: a design decision is under")))
    intercept[IllegalArgumentException](books.under(onlyGood))
    // (a node names its parents when it is built, from nodes built before it: no cycle can be written)
  }

  test("the implementation is also run on combinations of the examples' inputs") {
    val two = Node.contract(picks)("Two", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(shelfParts*)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
    // passes every example, but returns the whole shelf when asked for one book from several
    val kb = shelfWith(two).implement(two)((s, n) => if s.size > 1 && n == 1 then s else s.filter(_.pages >= minPages.value).take(n))
    val rs = kb.exampleResults(two)
    assertEquals(rs.take(3).flatMap(_.implementation), List("ok", "ok", "ok"))
    val generated = rs.drop(3)
    assertEquals(generated.size, 1)
    assert(generated.head.implementation.exists(_.contains("breaks the contract")), generated)
  }

  test("a cross-cutting invariant is a claim kept by the contracts that name it, on examples, generated calls and at run time") {
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "Readers carry what they asked for.")(
      (asked, picked) => picked <= asked).under(onlyGood)
    val kept = Node.contract(picks)("Kept", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(shelfParts*)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
    val kb = shelfWith(kept, atMostN).implement(kept)((s, n) => s.filter(_.pages >= minPages.value).take(n))
    assertEquals(kb.problems, Nil)
    // keeping makes the contract a part of the invariant
    assertEquals(kb.parts(atMostN).map(_.id), List("Kept"))
    assert(kb.exampleResults(kept).forall(_.implementation.contains("ok")), kb.exampleResults(kept))
    // every long book, twice: meets the post, breaks the invariant when one is asked for
    val bad = kb.implement(kept)((s, n) => s.filter(_.pages >= minPages.value) ++ s.filter(_.pages >= minPages.value))
    assert(bad.exampleResults(kept).flatMap(_.implementation).exists(_.contains("breaks the invariant AtMostN")), bad.exampleResults(kept))
    val run = bad.service(kept)(minPages.bind(100))
    intercept[ContractViolation](run(List(Book("Long", 300)), 1))
    // every contract whose result can hold what the rule is about keeps it or says why not; an invariant nobody keeps is a problem
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).under(onlyGood)
    val unkept = shelfWith(pick, fromShelf).problems.map(_.message)
    assert(unkept.exists(_.contains("no contract keeps")), unkept)
    assert(unkept.exists(_.startsWith("Pick: keep FromShelf")), unkept)
    val exempt = shelfWith(pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b))), kept.exempt(fromShelf, "the shelf is checked by Pick"), fromShelf, atMostN)
    assertEquals(exempt.problems, Nil)
    // a rule about numbers does not reach a contract that returns books
    assert(!shelfWith(pick, kept, atMostN).problems.exists(_.message.startsWith("Pick: keep AtMostN")))
    // an invariant scoped to another subtree does not apply
    val scoped = Node.invariant[List[Book], Book]("Scoped", "s", "w", scope = List(everyLong))((shelf, b) => shelf.contains(b)).under(onlyGood)
    assert(shelfWith(pick, scoped).problems.exists(_.message.startsWith("Pick: keep Scoped")))
  }

  test("two different parameters with one name are a problem") {
    val other = Param[Int]("minPages", "the pages a reader can carry")
    val c = Node.contract(picks)("Clash", "s", "w")((shelf, n, picked) => picked.length <= other.value).under(shelfParts*)
    assert(shelfWith(c).problems.exists(_.message.startsWith("two different parameters are named minPages")), shelfWith(c).problems)
  }

  test("examples are checked against the contract and the registered implementation") {
    val rs = shelfKb.exampleResults(pick)
    assertEquals(rs.map(r => (r.contract, r.implementation)), List.fill(4)(("ok", Some("ok"))))
    // a useless implementation: it does not do what was decided
    val lazyKb = shelfKb.implement(pick)((_, _) => Nil)
    assertEquals(lazyKb.exampleResults(pick).head.implementation, Some("returned List()"))
    // a contract that refuses what was decided
    val strict = Node.contract(picks)("Strict", "Nothing is picked.", "w")((_, _, picked) => picked.isEmpty)
      .examples(minPages.bind(100))(expect(List(Book("Long", 300)), 1, List(Book("Long", 300)), "the long book"))
    assertEquals(strict.checkExamples(None).head.contract, "the contract refuses it")
  }

  test("every node says why") {
    val noWhy = Node.claim("NoWhy", "s", " ")(forall((x: BigInt) => sq(x) >= 0)).under(onlyGood)
    assert(shelfWith(pick, noWhy).problems.exists(_.message.contains("say why")))
  }

  test("an enforced implementation returns results that meet the contract, or fails closed") {
    val ok = pick.enforce((shelf, n) => shelf.filter(_.pages >= 100))(minPages.bind(100))
    assertEquals(ok(List(Book("a", 50), Book("b", 150)), 5), List(Book("b", 150)))
    val bad = pick.enforce((shelf, n) => shelf.take(n))(minPages.bind(100))
    intercept[ContractViolation](bad(List(Book("a", 50)), 1))
    val unbound = pick.enforce((shelf, n) => shelf)()
    intercept[IllegalStateException](unbound(List(Book("a", 500)), 1))
  }

  test("service binds each operation with code to that code, and each defined term to its definition") {
    // Again's code calls the shelf service's operation: the service runs PickPromise's code for it
    val s = callsKb.service(againC)(minPages.bind(100))
    assertEquals(s(List(Book("Long", 300), Book("Short", 20)), 5), List(Book("Long", 300)))
    // a contract stated in a defined term: the term is bound to its definition where it runs
    val longEnough = Param[Book => Boolean]("longEnough", "whether a book is long enough for readers")
    val lengths = Node.definition("Lengths", "A book is long enough when it has the pages readers asked for.", "w")(
      longEnough := ((b: Book) => b.pages >= minPages.value))
    val byTerm = Node.contract(picks)("ByTerm", "Picked books are long enough.", "w")((shelf, n, picked) => picked.forall(b => longEnough(b)))
      .under(shelfParts*)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300)), 1, List(Book("Long", 300)), "the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "not a short one"))
    val kb = shelfWith(byTerm, lengths).implement(byTerm)((shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    assert(kb.exampleResults(byTerm).forall(r => r.contract == "ok" && r.implementation.contains("ok")), kb.exampleResults(byTerm))
    assertEquals(kb.service(byTerm)(minPages.bind(100))(List(Book("Long", 300), Book("Short", 20)), 1), List(Book("Long", 300)))
    intercept[IllegalStateException](kb.service(byTerm)())
  }

  test("a term defined by an expression, not a function, is evaluated where it is used, under the bindings in force") {
    val shelfNow = Param[List[Book]]("shelfNow", "the books on the shelf now")
    val onShelf = Param[Int]("onShelf", "how many books the shelf holds")
    // Evaluated when the model loads, the definition would read shelfNow before anything binds it.
    val counting = Node.definition("Counting", "The shelf holds as many books as are on it.", "w")(onShelf := shelfNow.value.length)
    val term = counting.substs.head.term.get
    assertEquals(term.body, "((shelfNow).length : Int)")
    assertEquals(Bindings.within(Seq(shelfNow.bind(List(Book("A", 100), Book("B", 200)))))(term.value), 2)
    assertEquals(Bindings.within(Seq(shelfNow.bind(Nil)))(term.value), 0)
    // As service and the examples bind it: the defined term, under the values bound with it.
    val kb = shelfWith(pick, counting)
    assertEquals(Bindings.within(shelfNow.bind(List(Book("A", 100))) +: kb.definitionBindings)(onShelf.value), 1)
    intercept[IllegalStateException](Bindings.within(kb.definitionBindings)(onShelf.value))
  }

  test("an assumption whose terms are bound is checked when the service starts, and when its values change") {
    val positive = Node.assumption("PositiveLength", "Readers ask for books of at least one page.", why = "A length of zero would let empty books in.")(
      minPages.value > 0).under(onlyLong)
    val kb = shelfWith(pick, positive).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    intercept[ContractViolation](kb.service(pick)(minPages.bind(0)))
    var min = 100
    val s = kb.service(pick)(minPages.bind(min))
    assertEquals(s(List(Book("Long", 300)), 1), List(Book("Long", 300)))
    min = 0
    val e = intercept[ContractViolation](s(List(Book("Long", 300)), 1))
    assert(e.getMessage.contains("PositiveLength"), e.getMessage)
    // an assumption over a quantifier cannot be computed: it is trusted only
    val world = Node.assumption("Shelved", "Every book has a title.", why = "The library labels books.")(forall((b: Book) => b.title != "")).under(onlyLong)
    assert(shelfWith(pick, world).implement(pick)((shelf, n) => shelf).runtimeAssumptions.head.holds())
  }

  test("an assumption names its idea section, on a fact or on an operation") {
    val fact = Node.assumption("LongShelf", "Readers ask for books of at least a page.", why = "An empty book is not a book.",
      idea = "Picking")(minPages.value >= 1)
    val port = Node.assumption(fetch)("Port", "The service returns books of the shelf.", why = "Books come from a service.", idea = "Picking")(
      (shelf, n, r) => r.forall(b => shelf.contains(b)))
    assertEquals((fact.ideaSection, port.ideaSection), ("Picking", "Picking"))
    assertEquals(port.op.map(_.name), Some("fetch"))
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
    val lazyPick = Node.contract(picks)("LazyPick", "s", "w")((_, _, picked) => picked.isEmpty).under(shelfParts*)
      .examples(minPages.bind(100))(expect(Nil, 1, Nil, "nothing"), reject(List(Book("L", 300)), 1, List(Book("L", 300)), "x"))
    assert(shelfWith(lazyPick).problems.exists(_.message.contains("always returns it")))
  }

  test("production code beside a proven define runs, and is checked against the define and the contract") {
    val good = shelfKb.implementProven(pick)(longOnes, (shelf, n) => shelf.filter(b => !(b.pages < minPages.value)))
    assert(good.exampleResults(pick).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), good.exampleResults(pick))
    assert(!good.implementation(pick).get.provenCode)
    // returning nothing is not what the proven define returns
    val lazyOne = shelfKb.implementProven(pick)(longOnes, (shelf, n) => List.empty[Book])
    assert(lazyOne.exampleResults(pick).exists(_.implementation.exists(_.contains("where the proven define returns"))), lazyOne.exampleResults(pick))
    // and at run time every result is checked against the contract
    val s = good.service(pick)(minPages.bind(100))
    assertEquals(s(List(Book("Long", 300)), 1), List(Book("Long", 300)))
  }
