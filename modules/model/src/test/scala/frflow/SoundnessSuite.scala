package frflow

import frflow.fixtures.*

/** What would let the Scala that runs and the Lean that is proven say different things, refused. */
class SoundnessSuite extends munit.FunSuite:
  private val limit = Param[BigInt]("limit", "the most a reader may borrow")

  /** Steps on the stock, comparing what it holds with the limit. */
  private def underLimit(d: Term[BigInt]): Flow[Boolean] =
    for
      c <- stock.count
      ok = c + d < limit.value
    yield ok

  test("a parameter's value read while a term is built is refused: it would be fixed in both the Lean and the Scala") {
    val frozen = Lifted.lambda((x: Term[BigInt]) => x < limit.value, List(summon[LeanType[BigInt]]), "")
    val e = intercept[IllegalStateException](Bindings.within(Seq(limit.bind(10)))(frozen.body))
    assert(e.getMessage.contains("limit.value is read while a model is built"), e.getMessage)
    assert(e.getMessage.contains("use limit itself as a term"), e.getMessage)
    // In a flow's steps too.
    val inFlow = Def(Lifted.flow(underLimit, List(summon[LeanType[BigInt]]), "underLimit"), summon[LeanType[Boolean]], Some("underLimit"), isFlow = true)
    intercept[IllegalStateException](Bindings.within(Seq(limit.bind(10)))(inFlow.lifted.body))
  }

  test("the parameter as a term follows its binding, in Lean and in Scala") {
    val live = Lifted.lambda((x: Term[BigInt]) => x < limit, List(summon[LeanType[BigInt]]), "")
    assertEquals(live.body, "(x < limit)")
    val f = live.value.asInstanceOf[BigInt => Boolean]
    assert(Bindings.within(Seq(limit.bind(10)))(f(5)))
    assert(!Bindings.within(Seq(limit.bind(1)))(f(5)))
    // Plain code still reads the value in force.
    assertEquals(Bindings.within(Seq(limit.bind(3)))(limit.value), BigInt(3))
  }

  test("== between a term and anything does not compile; a term is not a value") {
    assert(compileErrors("""long(Book("a", 300)) == true""").contains("compare terms with ==="))
    assert(compileErrors("""long(Book("a", 300)) != false""").contains("compare terms with ==="))
    assert(compileErrors("""good(Book("a", 1).asInstanceOf[Item.T]) == true""").contains("compare terms with ==="))
    // The term a define gives on values is not the value: plain code that wants one does not compile.
    assert(compileErrors("""val b: Boolean = long(Book("a", 300))""").nonEmpty)
    assertEquals(long.fn(Book("a", 300)), true)
  }

  test("=== between functions is refused: Scala compares them by reference, Lean by their values") {
    val shown = Param[Book => Boolean]("shownAs", "a test of a function-valued parameter")
    val e = intercept[IllegalArgumentException](leanOf(shown === shown))
    assert(e.getMessage.contains("between functions"), e.getMessage)
  }
