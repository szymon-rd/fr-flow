package frflow.project.program

import cats.effect.IO
import frflow.core.name.NodeId
import frflow.decision.review.{Cause, ReviewState}
import frflow.decision.rules.Command
import frflow.dsl.example.FrFlowExamples
import frflow.project.Projects
import frflow.project.pipeline.{Contents, TestKeys}
import frflow.project.port.RunCode

/** A formula changed under the same sentence, and an example changed: each is the developer's text, so the node's
  * content moves, its decision is reviewed again and its test report is no longer current.
  */
class VersionsSuite extends munit.CatsEffectSuite:
  private val id = NodeId("nonNegative")
  private val before = Projects.elaborated(Versions.Before.kb)
  private val after = Projects.elaborated(Versions.After.kb)

  test("a changed formula, its sentence the same, moves the content, reviews the decision, and tests it again") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, before, Nil)
      tested <- TestProgram[IO](p.files, RunCode.inline[IO], Nil)(a, None)
      out    <- DecideProgram(p.ports)(tested._2.subjects, Command.Accept(List(id), "never below zero", Nil,
                  Map.empty), "ann")
      was    <- Projects.analysed(p, before, Nil)
      now    <- Projects.analysed(p, after, Nil)
    yield
      assert(out.isRight, out)
      assertEquals(List(was, now).map(x => Contents.of(x.decided, id).text("formula")),
        List("forall((n: Term[BigInt]) => d(n) >= 0)", "forall((n: Term[BigInt]) => d(n) >= 1)"))
      assertNotEquals(Contents.of(was.decided, id).ref, Contents.of(now.decided, id).ref)
      assertEquals(was.reading.state(id), ReviewState.Accepted)
      assertEquals((now.reading.state(id), now.reading.causes(id).contains(Cause.Self)), (ReviewState.Review, true))
      assertNotEquals(TestKeys.of(was, id), TestKeys.of(now, id))
      assertEquals((was.tested(id).isDefined, now.tested(id)), (true, None))
  }

  private def examples(x: FrFlowExamples) = x.elaborated.toEither.fold(e => fail(e.toString), identity)

  test("an example's fact is its text; a changed one tests the nodes again") {
    val (one, two) = (examples(Versions.Before.Shown()), examples(Versions.After.Shown()))
    for
      p <- Projects.inMemory(Map.empty)
      a <- Projects.analysed(p, before, one)
      b <- Projects.analysed(p, before, two)
    yield
      assertEquals((one ++ two).map(_.fact.source.value), List("d(1) is 1", "d(2) is 2"))
      assertNotEquals(TestKeys.of(a, id), TestKeys.of(b, id))
  }
