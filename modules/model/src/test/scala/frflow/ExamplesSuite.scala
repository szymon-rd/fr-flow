package frflow

import frflow.fixtures.*

/** Examples, run against the contract and the code, and the calls generated beyond them. */
class ExamplesSuite extends munit.FunSuite:

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

  test("what a contract does not promise: an input it never reads, an empty result it always accepts") {
    // PickPromise: picked books come from the shelf and are long; nothing says some must be picked
    assertEquals(shelfKb.limits(pickPromise), List("the result may not depend on `n`: the contract never looks at it",
      "an empty result (None or Nil) always satisfies it: it never requires the system to return anything"))
    assertEquals(shelfKb.limits(pick), List("the result may not depend on `n`: the contract never looks at it"))
    assertEquals(shelfKb.limits(onlyGood), Nil)
  }

  test("generated calls are only listed when they fail, at most ten, and code that throws is a finding") {
    assertEquals(shelfKb.generated(pick), Nil)
    val throwing = shelfKb.implement(pick)((shelf, n) => if shelf.size > 1 && n == 1 then sys.error("boom") else shelf.filter(_.pages >= minPages.value))
    val two = Node.contract(picks)("Two", "s", "w")((shelf, n, picked) => picked.forall(b => shelf.contains(b)))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("X", 1)), "never one off the shelf"))
    val rs = shelfWith(two).implement(two)((s, n) => if s.size > 1 && n == 1 then sys.error("boom") else s.filter(_.pages >= minPages.value)).generated(two)
    assertEquals(rs.map(_.implementation), List(Some("error: boom")))
    assertEquals(rs.map(_.example.call), List("(List(Book(\"Long\", 300), Book(\"Short\", 20)), 1) ⇒ no result"))
    assert(throwing.generated(pick).isEmpty) // the examples' inputs never ask for one book of two
  }
