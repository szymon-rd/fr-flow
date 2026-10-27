package frflow.dsl.example

import frflow.dsl.kb.KnowledgeBase
import frflow.dsl.node.Node
import frflow.dsl.term.TermSyntax.{&&, True, ||}

/** An example's fact is the text the developer wrote, as a claim's formula is; a knowledge base, the file it is
  * assembled in.
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

  test("a knowledge base records the file it is assembled in, as its nodes record theirs") {
    val t = kb.elaborated.toEither.fold(e => fail(e.toString), _.theory)
    assertEquals(t.writtenIn, t.nodes.headOption.map(_.at.file))
    assert(t.writtenIn.exists(_.value.endsWith("ExampleSourceSuite.scala")), t.writtenIn)
  }
