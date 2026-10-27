package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.testing.{Plan, PropertyTests, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.report.Note

/** What a report says beside its outcome, and what its coverage counts: each generator given; the examples' values a
  * given generator never makes; and the cases the examples show of the call, counted before the generated ones.
  */
class NotesSuite extends munit.FunSuite:
  private val e = rooms.elaborated.fold(es => fail(es.toString), identity)
  private val examples = GrantedExamples().elaborated.fold(es => fail(es.toString), identity)
  private val draw = Derive.of(e, examples)

  test("a given generator that never makes the examples' values is said, with those values") {
    val never = draw.notes.collect { case Note.NeverMade(ty, vs) => ty -> vs.size }.toMap
    assert(never.get(LeanType[Booking].ty).exists(_ > 0), draw.notes)
    assert(draw.notes.exists { case Note.Given(m) => m.says.contains("Oak or Elm"); case _ => false }, draw.notes)
  }

  test("the cases the examples show of granted are counted in the coverage before any generated case") {
    val tests = PropertyTests(Semantics(e), e.theory)
    val none = Plan(Settings(0, Seed(1)), Nil)
    val alone = tests.of(NodeId("grantWhenNoOverlap"), none, draw).map(_.unreached).getOrElse(fail("not tested"))
    val shown = tests.of(NodeId("grantWhenNoOverlap"), none, draw, examples).map(_.unreached)
      .getOrElse(fail("not tested"))
    assert(shown.size < alone.size, s"$shown of $alone")
  }

  private val answer = Definition[BigInt]("the answer the service gives")
  private val fixed = Node.claim("The service answers 42.")(answer === BigInt(42))

  test("a claim with no input whose code is given nothing has nothing to vary, and says so") {
    val kb = FrModel("Answer")(fixed).implementTested(answer)(_ => BigInt(42))
    val k = kb.elaborated.fold(es => fail(es.toString), identity)
    val report = PropertyTests(Semantics(k), k.theory).of(NodeId("fixed"), Plan(Settings(3, Seed(1)), Nil),
      Derive.of(k, Nil))
    assert(report.exists(_.notes.contains(Note.NothingToVary)), report)
  }
