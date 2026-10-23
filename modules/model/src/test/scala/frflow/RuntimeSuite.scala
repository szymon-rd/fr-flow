package frflow

import frflow.fixtures.*

/** The running system: contracts enforced on every call, the wiring of `service`, assumptions checked. */
class RuntimeSuite extends munit.FunSuite:

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

  test("a function a call reads answers each question once, and only what is read is loaded") {
    val asked = scala.collection.mutable.ListBuffer.empty[Int]
    val square = Param[Int => Int]("square", "a slow service")
    val cell = Cell(square.bind((x: Int) => { asked += x; x * x }))
    assert(!cell.loaded)
    val f = cell.get.asInstanceOf[Int => Int]
    assertEquals((f(3), f(3), f(4)), (9, 9, 16))
    assertEquals(asked.toList, List(3, 4))
    assert(cell.loaded)
  }

  test("a parameter read where nothing binds it fails with its name") {
    val e = intercept[IllegalStateException](minPages.value)
    assert(e.getMessage.contains("minPages"), e.getMessage)
    assertEquals(Bindings.within(Seq(minPages.bind(7)))(Bindings.within(Seq(minPages.bind(8)))(minPages.value) + minPages.value), 15)
  }
