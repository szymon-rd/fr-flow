package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.name.NodeId
import frflow.decision.review.{Cause, ReviewState}
import frflow.decision.rules.Command
import frflow.dsl.example.FrFlowExamples
import frflow.project.Projects
import frflow.project.pipeline.{Analysis, Contents, TestKeys}
import frflow.project.port.RunCode

/** A formula changed under the same sentence, written inline or through a helper of the developer's: what it means
  * moves, so its decision is reviewed again and its test report is no longer current; its Scala spaced out or its
  * variable renamed means the same, and is not reviewed. An example changed is tested again.
  */
class VersionsSuite extends munit.CatsEffectSuite:
  private val id = NodeId("nonNegative")
  private val before = Projects.elaborated(Versions.Before.kb)
  private val after = Projects.elaborated(Versions.After.kb)

  /** `first` tested and its node accepted, then the analyses of `first` and `second` over the same ports. */
  private def accepted(first: Elaborated, second: Elaborated): IO[(Analysis, Analysis)] =
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, first, Nil)
      tested <- TestProgram[IO](p.files, RunCode.inline[IO], Nil)(a, None)
      out    <- DecideProgram(p.ports)(tested._2.subjects, Command.Accept(List(id), "never below zero", Nil,
                  Map.empty), "ann")
      _       = assert(out.isRight, out)
      was    <- Projects.analysed(p, first, Nil)
      now    <- Projects.analysed(p, second, Nil)
    yield (was, now)

  private def content(a: Analysis) = Contents.of(a.canonical, id)

  test("a changed formula, its sentence the same, moves the content, reviews the decision, and tests it again") {
    accepted(before, after).map { (was, now) =>
      assertEquals(List(was, now).map(content(_).text("written")),
        List("forall((n: Term[BigInt]) => d(n) >= 0)", "forall((n: Term[BigInt]) => d(n) >= 1)"))
      assertNotEquals(content(was).text("formula"), content(now).text("formula"))
      assertEquals(was.reading.state(id), ReviewState.Accepted)
      assertEquals((now.reading.state(id), now.reading.causes(id).contains(Cause.Self)), (ReviewState.Review, true))
      assertNotEquals(TestKeys.of(was, id), TestKeys.of(now, id))
      assertEquals((was.tested(id).isDefined, now.tested(id)), (true, None))
    }
  }

  test("a helper's body changed, the formula calling it as it was: the decision is reviewed") {
    accepted(Projects.elaborated(Versions.Helped.kb), Projects.elaborated(Versions.HelpedAgain.kb)).map { (was, now) =>
      assertEquals(List(was, now).map(content(_).text("written")), List("rule", "rule"))
      assertNotEquals(content(was).text("formula"), content(now).text("formula"))
      assertEquals((now.reading.state(id), now.reading.causes(id)), (ReviewState.Review, List(Cause.Self)))
    }
  }

  test("a formula's Scala spaced out, or its variable renamed: what it means is the same, and is not reviewed") {
    List(Versions.Spaced.kb, Versions.Renamed.kb).traverse(kb => accepted(before, Projects.elaborated(kb))).map(
      _.foreach { (was, now) =>
        assertNotEquals(content(was).text("written"), content(now).text("written"))
        assertEquals(content(was).text("formula"), content(now).text("formula"))
        assertEquals(now.reading.state(id), ReviewState.Accepted)
      })
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
