package frflow

import frflow.fixtures.*

/** The one generator of what is tried beyond the examples. */
class ProbesSuite extends munit.FunSuite:

  test("values near a value: the boundaries and next to them, a list shortened or grown, a field changed") {
    assertEquals(Probes.near(5, List(BigInt(3))), List(3, 0, 6, 4, -5))
    assertEquals(Probes.near(List(1), Nil), List(Nil, List(1, 1), List(1, 0), List(1, 2)))
    assertEquals(Probes.near(Book("A", 1), Nil), List(Book("", 1), Book("AA", 1), Book("A", 0), Book("A", 2), Book("A", -1)))
    assertEquals(Probes.near(None, Nil), Nil)
  }

  test("inputs near the examples' that no example asks, and every combination of the examples' inputs") {
    val cases = pick.cases
    val inputs = Probes.inputs(cases)
    assert(inputs.nonEmpty)
    assert(inputs.forall(i => !cases.exists(e => (e.a, e.b) == i)))
    assertEquals(inputs.distinct, inputs)
    // the numbers the examples hold are tried as the other input
    assert(inputs.exists(_._2 == 300), inputs)
    assertEquals(Probes.boundaries(cases), List(BigInt(300), BigInt(20), BigInt(5)))
    val combos = Probes.combinations(cases)
    assertEquals(combos.size, cases.map(_.a).distinct.size * cases.map(_.b).distinct.size)
  }

  test("variations of a parameter value: at most eight") {
    val table = List(Book("A", 100), Book("B", 200), Book("C", 300))
    val vs = Probes.variations(table, pick.cases)
    assertEquals(vs, Probes.near(table, Probes.boundaries(pick.cases) ++ Probes.numbers(table)).take(8))
    assert(vs.nonEmpty && !vs.contains(table))
    assertEquals(Probes.variations((1, 2, 3), Nil).size, 8) // nine near it, eight kept
  }
