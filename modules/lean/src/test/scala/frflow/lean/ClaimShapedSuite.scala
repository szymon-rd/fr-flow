package frflow
package lean

import frflow.fixtures.*

/** A contract written as a claim is the contract written as a lambda over the call: the same Lean, examples and tests. */
class ClaimShapedSuite extends munit.FunSuite:
  private val statement = "A call returns exactly the long enough books of the shelf."
  private def cases = List(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    never(List(Book("Long", 300)), 5, Nil, "a long book is not left on the shelf"))

  private val asLambda = Node.contract(picks)("Pick", statement)((shelf, n, result) =>
    result.forall(b => shelf.contains(b) && b.pages >= minPages) && shelf.forall(b => b.pages >= minPages implies result.contains(b)))
    .refines(fromList, onlyLong, everyLong)
    .examples(minPages.bind(100))(cases*)

  private val asClaim = Node.contract("Pick", statement)(
    forall((shelf: Term[List[Book]], n: Term[Int]) =>
      picks(shelf, n).forall(b => shelf.contains(b) && b.pages >= minPages) &&
        shelf.forall(b => b.pages >= minPages implies picks(shelf, n).contains(b))))
    .refines(fromList, onlyLong, everyLong)
    .examples(minPages.bind(100))(cases*)

  private def kb(c: Node[(List[Book], Int) => List[Book]]) =
    shelfWith(c).implement(c)((shelf, n) => shelf.filter(_.pages >= minPages.value))
  private def buggy(c: Node[(List[Book], Int) => List[Book]]) =
    shelfWith(c).testedWith(TestSettings(100)).implement(c)((shelf, n) => shelf.filter(_.pages > minPages.value))

  test("the two forms give the same Lean, file by file") {
    val (a, b) = (Generate(kb(asLambda)), Generate(kb(asClaim)))
    assertEquals(b.files.keySet, a.files.keySet)
    a.files.foreach((path, lean) => assertNoDiff(b.files(path), lean, path))
    assertEquals(b.proofFile(asClaim, Nil), a.proofFile(asLambda, Nil))
  }

  test("the two forms give the same operation, examples and verdicts on the code") {
    assertEquals(asClaim.op.map(_.name), Some("picks"))
    assertEquals(asClaim.post.map(_.lean), asLambda.post.map(_.lean))
    assertEquals(kb(asClaim).problems, kb(asLambda).problems)
    val verdicts = (c: Node[?]) => c.checkExamples(None).map(r => (r.example.note, r.contract, r.implementation))
    assertEquals(verdicts(asClaim), verdicts(asLambda))
    val failure = (c: Node[(List[Book], Int) => List[Book]]) => buggy(c).test(c).flatMap(_.failure).map(f => (f.shown, f.why))
    assert(failure(asLambda).isDefined)
    assertEquals(failure(asClaim), failure(asLambda))
  }

  test("a formula of another shape does not compile, and says the shape") {
    val noOp = compileErrors("""Node.contract("C", "s")(forall((l: Term[List[Book]], n: Term[Int]) => l.isEmpty))""")
    assert(noOp.contains("applies no operation"), noOp)
    val two = compileErrors(
      """Node.contract("C", "s")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).isEmpty && shown(Nil, Book("a", 1))))""")
    assert(two.contains("applies picks and shown") || two.contains("applies shown and picks"), two)
    val other = compileErrors("""Node.contract("C", "s")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n + 1).isEmpty))""")
    assert(other.contains("applies one operation to its forall's variables, in order"), other)
    val swapped = compileErrors("""Node.contract("C", "s")(forall((n: Term[Int], l: Term[List[Book]]) => picks(l, n).isEmpty))""")
    assert(swapped.contains("in order"), swapped)
  }
