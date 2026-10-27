package frflow.dsl.example

import frflow.dsl.kb.KnowledgeBase
import frflow.dsl.node.Node
import frflow.dsl.term.TermSyntax.{&&, True, ||}

/** An example's fact is the text the developer wrote, as a claim's formula is: what a decision and a test report bind
  * moves with it.
  */
class ExampleSourceSuite extends munit.FunSuite:
  private val kb = KnowledgeBase("Holding")(Node.claim("Holds.")(True))

  private class Written extends FrFlowExamples(kb):
    example("either"):
      True ||   True
    example("both")(True && True)

  test("each example's fact is its source as written") {
    val facts = Written().elaborated.toEither.fold(e => fail(e.toString), identity).map(x => x.name -> x.fact.source
      .value)
    assertEquals(facts, List("either" -> "True ||   True", "both" -> "True && True"))
  }
