package frflow

/** The graph walks, on a small graph with a diamond and a cycle. */
class WalkSuite extends munit.FunSuite:
  // a → b, c; b → d; c → d; d → a (a cycle back to the start); e alone
  private val edges = Map("a" -> List("b", "c"), "b" -> List("d"), "c" -> List("d"), "d" -> List("a"), "e" -> Nil)
  private def next(v: String) = edges.getOrElse(v, Nil)

  test("breadth first: level by level, each once, the cycle closing on what was seen") {
    assertEquals(Walk.breadthFirst(next("a"), identity)(next), List("b", "c", "d", "a"))
    assertEquals(Walk.breadthFirst(List("e"), identity)(next), List("e"))
  }

  test("preorder: each before what it leads to") {
    assertEquals(Walk.preorder(List("a"), identity)(next), List("a", "b", "d", "c"))
  }

  test("postorder: what each leads to before it, a cycle cut where it closes") {
    assertEquals(Walk.postorder(List("a", "e"), identity)(next), List("d", "b", "c", "a", "e"))
    // by key: two values with one key are one
    assertEquals(Walk.postorder(List("x1", "x2", "y"), _.head)(_ => Nil), List("x1", "y"))
  }
