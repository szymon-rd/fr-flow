package whole

import frflow.core.graph.Walk
import frflow.dsl.kb.FrModel

/** The examples as written: each FrModel elaborates, the analyses find no problem in it, and its proofs do not go
  * round.
  */
class ExamplesSuite extends munit.FunSuite:
  private val all: List[(String, FrModel)] = List("rooms" -> rooms.rooms, "auth" -> auth.knowledge)

  test("each example elaborates, with no error") {
    assertEquals(all.map((name, kb) => name -> Theories.errors(kb)), all.map(_._1 -> Nil))
  }

  test("each example's examples elaborate, with no error") {
    val written = List(rooms.GrantedExamples(), auth.DecisionExamples())
    assertEquals(written.map(_.elaborated.fold(_.iterator.toList, _ => Nil)), List.fill(written.size)(Nil))
    assertEquals(written.map(_.examples.size), List(2, 5))
  }

  test("the examples are valid as written") {
    assertEquals(all.map((_, kb) => Theories.problems(kb)), List.fill(all.size)(Nil))
  }

  test("no example's proofs go round: what each node is proven from, followed down, never reaches it") {
    all.foreach { (name, kb) =>
      val r = Theories.resolved(kb)
      val ids = r.theory.nodes.map(_.node.id)
      assertEquals(ids.filter(id => Walk.breadthFirst(r.provenFrom(id), identity)(r.provenFrom).contains(id)), Nil,
        name)
    }
  }
