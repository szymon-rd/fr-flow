package frflow
package lean

import frflow.fixtures.*

/** A contract written as a claim is the contract written as a lambda over the call: the same Lean, examples and tests. */
class ClaimShapedSuite extends munit.FunSuite:
  private val statement = "A call returns exactly the long enough books of the shelf."
  private def cases = List(
    allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    forbids(List(Book("Long", 300)), 5, Nil, "a long book is not left on the shelf"))

  private object asLambda:
    val pick = Node.contract(picks)(statement)((shelf, n, result) =>
      result.forall(b => shelf.contains(b) && b.pages >= minPages) && shelf.forall(b => b.pages >= minPages implies result.contains(b)))
      .refines(fromList, onlyLong, everyLong)
      .examples(minPages.bind(100))(cases*)

  private object asClaim:
    val pick = Node.contract(statement)(
      forall((shelf: Term[List[Book]], n: Term[Int]) =>
        picks(shelf, n).forall(b => shelf.contains(b) && b.pages >= minPages) &&
          shelf.forall(b => b.pages >= minPages implies picks(shelf, n).contains(b))))
      .refines(fromList, onlyLong, everyLong)
      .examples(minPages.bind(100))(cases*)

  private def kb(c: Node[(List[Book], Int) => List[Book]]) =
    shelfWith(c).implementTested(c)((shelf, n) => shelf.filter(_.pages >= minPages.value))
  private def buggy(c: Node[(List[Book], Int) => List[Book]]) =
    shelfWith(c).testedWith(TestSettings(100)).implementTested(c)((shelf, n) => shelf.filter(_.pages > minPages.value))

  test("the two forms give the same Lean, file by file") {
    val (a, b) = (Generate(kb(asLambda.pick)), Generate(kb(asClaim.pick)))
    assertEquals(b.files.keySet, a.files.keySet)
    a.files.foreach((path, lean) => assertNoDiff(b.files(path), lean, path))
    assertEquals(b.proofFile(asClaim.pick, Nil), a.proofFile(asLambda.pick, Nil))
  }

  test("the two forms give the same operation, examples and verdicts on the code") {
    assertEquals(asClaim.pick.op.map(_.name), Some("picks"))
    assertEquals(asClaim.pick.post.map(_.lean), asLambda.pick.post.map(_.lean))
    assertEquals(kb(asClaim.pick).problems, kb(asLambda.pick).problems)
    val verdicts = (c: Node[?]) => c.checkExamples(None).map(r => (r.example.note, r.contract, r.implementation))
    assertEquals(verdicts(asClaim.pick), verdicts(asLambda.pick))
    val failure = (c: Node[(List[Book], Int) => List[Book]]) => buggy(c).test(c).flatMap(_.failure).map(f => (f.shown, f.why))
    assert(failure(asLambda.pick).isDefined)
    assertEquals(failure(asClaim.pick), failure(asLambda.pick))
  }

  test("a formula of another shape does not compile, and says the shape") {
    val noOp = compileErrors("""val c = Node.contract("s")(forall((l: Term[List[Book]], n: Term[Int]) => l.isEmpty))""")
    assert(noOp.contains("applies no operation"), noOp)
    val two = compileErrors("""val c = Node.contract("s")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n) === again(l, n)))""")
    assert(two.contains("applies picks and again") || two.contains("applies again and picks"), two)
    // another Param applied to other inputs is what the contract reads, not its operation
    val readsPickedFrom = Node.contract("s")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => pickedFrom(l, b))))
    assertEquals(readsPickedFrom.op.map(_.name), Some("picks"))
    val other = compileErrors("""val c = Node.contract("s")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n + 1).isEmpty))""")
    assert(other.contains("applies one operation to its forall's variables, in order"), other)
    val swapped = compileErrors("""val c = Node.contract("s")(forall((n: Term[Int], l: Term[List[Book]]) => picks(l, n).isEmpty))""")
    assert(swapped.contains("in order"), swapped)
  }
