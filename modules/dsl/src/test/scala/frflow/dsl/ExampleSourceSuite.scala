package frflow.dsl

import frflow.dsl.build.{ElabError, Fault, Site}
import frflow.dsl.example.*
import frflow.dsl.kb.FrModel
import frflow.dsl.node.Node
import frflow.dsl.term.TermSyntax.{&&, True, ||}

/** An example's fact is the text the developer wrote, as a claim's formula is; a FrModel, the file it is
  * assembled in.
  */
class ExampleSourceSuite extends munit.FunSuite:
  private val kb = FrModel("Holding")(Node.claim("Holds.")(True))

  private class Written extends FrFlowExamples(kb):
    example("either"):
      True ||   True
    example("both")(True && True)

  private object One:
    class Same extends FrFlowExamples(kb):
      example("one")(True)
  private object Two:
    class Same extends FrFlowExamples(kb):
      example("two")(True)

  test("two classes of examples of one model of one name are refused: their examples' theorems would be one") {
    FrFlowExamples.elaborated(List(One.Same(), Two.Same())).toEither.left.map(_.iterator.toList) match
      case Left(List(ElabError(Site.Example("Same"), Fault.ExampleSetsClash("Same", cs)))) => assertEquals(cs.size, 2)
      case other                                                                         => fail(other.toString)
    assert(FrFlowExamples.elaborated(List(One.Same(), Written())).isValid)
  }

  test("a class's name with letters not ASCII is a Lean identifier with a hash of its full name, two kept apart") {
    assertEquals(FrFlowExamples.identifier("GrantedExamples", "rooms.GrantedExamples"), "GrantedExamples")
    val (one, two) = (FrFlowExamples.identifier("例", "a.例"), FrFlowExamples.identifier("例", "b.例"))
    assert(one.startsWith("Examples") && one != two && (one + two).forall(c => c.isLetterOrDigit && c < 128),
      s"$one $two")
  }

  test("each example's fact is its source as written") {
    val facts = Written().elaborated.toEither.fold(e => fail(e.toString), identity).map(x => x.name -> x.fact.source
      .value)
    assertEquals(facts, List("either" -> "True ||   True", "both" -> "True && True"))
  }

  test("a FrModel records the file it is assembled in, as its nodes record theirs") {
    val t = kb.elaborated.toEither.fold(e => fail(e.toString), _.theory)
    assertEquals(t.writtenIn, t.nodes.headOption.map(_.at.file))
    assert(t.writtenIn.exists(_.value.endsWith("ExampleSourceSuite.scala")), t.writtenIn)
  }
