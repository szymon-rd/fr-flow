package frflow

import frflow.fixtures.*

/** Operations of one and three inputs, and a flow of two: examples, generated tests with shrinking, invariants and the
  * running service, as for two.
  */
class AritySuite extends munit.FunSuite:
  private val settings = TestSettings(cases = 300, seed = 7)

  test("one input: examples, a generated test that finds a bug and shrinks it, the running service") {
    val kb = clampKb.implementProven(clamp)(clampAtZero)
    assertEquals(kb.problems, Nil)
    assertEquals(kb.exampleResults(clamp).map(r => (r.contract, r.implementation)), List.fill(3)(("ok", Some("ok"))))
    assertEquals(clamp.cases.map(_.call), List("(5) ⇒ 5", "(-3) ⇒ 0", "(-3) ⇒ -3"))
    // plain code: tested on generated values
    assertEquals(clampKb.implement(clamp)(x => x.max(0)).testedWith(settings).test(clamp).flatMap(_.failure), None)
    val f = clampKb.implement(clamp)(x => x.abs).testedWith(settings).test(clamp).flatMap(_.failure).getOrElse(fail("the bug was not found"))
    assertEquals(f.shown, "x = -1")
    assert(f.why.contains("Clamp forbids"), f.why)
    // the service: a function of one input, every result checked
    assertEquals(kb.service(clamp)()(BigInt(-2)), BigInt(0))
    intercept[ContractViolation](clampKb.implement(clamp)(x => x).service(clamp)()(BigInt(-2)))
  }

  test("three inputs: examples, a generated test that finds a bug and shrinks it, the running service") {
    val kb = grantKb.implementProven(grant)(grantIfMember)
    assertEquals(kb.problems, Nil)
    assert(kb.exampleResults(grant).forall(r => r.contract == "ok" && r.implementation.contains("ok")), kb.exampleResults(grant))
    assertEquals(grant.cases.head.call, """(List("ann"), "ann", "bob") ⇒ List("ann", "bob")""")
    val good = grantKb.implement(grant)((acl, by, who) => if acl.contains(by) then acl :+ who else acl)
    assertEquals(good.testedWith(settings).test(grant).flatMap(_.failure), None)
    // someone off the list makes the code drop the first member
    val bad = grantKb.implement(grant)((acl, by, who) => if acl.contains(by) then acl :+ who else acl.drop(1))
    val f = bad.testedWith(settings).test(grant).flatMap(_.failure).getOrElse(fail("the bug was not found"))
    assert(f.shown.matches("""acl = List\("[^"]*"\), by = "[^"]*", who = "[^"]*""""), f.shown)
    assert(f.why.startsWith("returned List()"), f.why)
    assert(f.why.contains("Grant forbids"), f.why)
    val s = kb.service(grant)()
    assertEquals(s(List("ann"), "ann", "bob"), List("ann", "bob"))
    intercept[ContractViolation](bad.service(grant)()(List("ann"), "eve", "bob"))
  }

  test("an invariant kept by a contract of three inputs, through a view of its call") {
    assertEquals(betweenKb.problems, Nil)
    assertEquals(betweenKb.parts(inStock).map(_.id), List("PickBetween"))
    assert(betweenKb.exampleResults(pickBetween).forall(_.contract == "ok"), betweenKb.exampleResults(pickBetween))
    val shelf = List(Book("A", 50))
    assertEquals(pickBetween.broken(List(shelf, 0, 100), List(Book("C", 60))), Some("InStock"))
    assertEquals(pickBetween.broken(List(shelf, 0, 100), shelf), None)
    // a generated call breaking it is found
    val off = betweenKb.implement(pickBetween)((s, lo, hi) => List(Book("C", lo))).testedWith(settings).test(pickBetween)
    assert(off.flatMap(_.failure).exists(f => f.why.contains("PickBetween forbids") || f.why.contains("InStock")), off)
  }

  test("a flow of two inputs: its examples run on the models and on an implementation") {
    assertEquals(deliveriesKb.problems, Nil)
    // the three on the models; the two expects on the stock's own implementation (a counter) too
    assertEquals(deliveriesKb.exampleResults(twoDeliveries).map(r => (r.contract, r.implementation)), List.fill(5)(("ok", Some("ok"))),
      deliveriesKb.exampleResults(twoDeliveries))
    assertEquals(twoDeliveries.cases.head.call, "(2, 3, World(StockModel = 10)) ⇒ Tuple2(15, World(StockModel = 15))")
  }

  test("no input: examples under bindings, a generated test that finds a bug and shrinks it, the running service") {
    val kb = gaugeKb.implementProven(shows)(showRaw)
    assertEquals(kb.problems, Nil)
    assertEquals(kb.exampleResults(shows).map(r => (r.contract, r.implementation)), List.fill(3)(("ok", Some("ok"))))
    assertEquals(shows.cases.head.call, "() ⇒ 5")
    assertEquals(gaugeKb.implement(shows)(() => rawReading.value.max(0)).testedWith(settings).test(shows).flatMap(_.failure), None)
    val f = gaugeKb.implement(shows)(() => rawReading.value).testedWith(settings).test(shows).flatMap(_.failure)
      .getOrElse(fail("the bug was not found"))
    assertEquals(f.shown, "given rawReading = -1")
    assertEquals(kb.service(shows)(rawReading.bind(-4))(), BigInt(0))
  }

  test("a flow of no input: its examples run on the models and on an implementation") {
    assertEquals(countingKb.problems, Nil)
    assertEquals(countingKb.exampleResults(counting).map(r => (r.contract, r.implementation)), List.fill(5)(("ok", Some("ok"))),
      countingKb.exampleResults(counting))
  }
