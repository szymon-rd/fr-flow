package frflow

import frflow.example.{ExampleSuite, Expected, Written}

/** Examples of what a knowledge base's Definitions do, written as tests:
  * {{{
  * class GrantedExamples extends FrFlowExamples(rooms):
  *   example("back to back: granted"):
  *     granted(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11)) is true
  * }}}
  * `sbt test` runs each against the code and against the claims on the Definition Scala can evaluate; `check` reads
  * them too, and evaluates each against those claims in Lean. They show how things work; nothing rests on them.
  */
abstract class FrFlowExamples(val knowledge: KnowledgeBase) extends munit.FunSuite, ExampleSuite:
  /** The examples, as munit holds them: each test carries its example as a tag. */
  def written: List[Written] = munitTests().toList.flatMap(_.tags.collect { case t: FrFlowExamples.Of => t.example })

  /** An example: a Definition called on values, and the answer it must give. */
  def example(name: String)(expected: => Expected)(using munit.Location): Unit =
    Written.of(name, expected, getClass.getName).fold(why => test(name)(fail(why)), checked(name, _))

  private def checked(name: String, w: Written)(using munit.Location): Unit =
    test(munit.TestOptions(name).tag(FrFlowExamples.Of(w))) {
      val kb = knowledge.withWritten(List(w))
      val claims = kb.nodes.filter(n => n.post.isDefined && n.op.exists(_ eq w.op))
      val failing = claims.flatMap(n => kb.exampleResults(n).filter(_.example.note == name).flatMap(r =>
        List(r.failing.map(f => s"${n.id}: $f"), r.implementation.filter(_ != "ok").map(i => s"the code $i")).flatten))
      assert(claims.nonEmpty, s"no claim is stated of ${w.op.name}: an example of it checks nothing")
      assert(failing.isEmpty, failing.distinct.mkString("; "))
    }

object FrFlowExamples:
  /** The tag a test written as an example carries: its example, for `check` to read. */
  final class Of(val example: Written) extends munit.Tag("frflow-example")
