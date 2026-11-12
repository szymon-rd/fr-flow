package frflow.project

import frflow.core.name.NodeId
import frflow.eval.{Calendar, CalendarExamples}
import frflow.eval.run.OnCode
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import frflow.testing.{Settings, Vectors}
import frflow.testing.report.Seed
import scala.concurrent.duration.*

/** Plain Scala read by `lifted`, checked by Rocq end to end: the calendar's decision, written as the Scala it runs
  * as, is proven to meet its claim over start and end times (`impl`, of the `def` printed from the term read), and
  * that claim gives the one over moments (`complete`, rooms' own proof of the step).
  */
class CalendarRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private lazy val proofs = List("grantWhenFree" -> Ported.resource("lifted/grantWhenFree.v"))

  test("the calendar's plain Scala is proven to meet its claims, and its examples hold".tag(Live)) {
    val examples = CalendarExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(Calendar.model), examples, proofs).map { r =>
      List("grantWhenFree", "grantWhenNoOverlap").foreach(n =>
        assertEquals(Ported.row(r, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r)}"))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      examples.foreach(e => assertEquals(r.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).map(_.status), Some(ObligationStatus.Shown), e.name))
    }
  }

  test("what the Scala gives on generated cases, the term gives and Rocq decides from the def printed".tag(Live)) {
    val e = Projects.elaborated(Calendar.model)
    val vectors = List(Calendar.noOverlap, Calendar.grantedCode).flatMap(Vectors.of(e, _, Settings(12, Seed(1))))
    Ported.run(e, vectors, proofs).map { r =>
      def lean(name: ObligationName) = r.wholeCheck.flatMap(_.results.find(_.name == name)).map(_.status)
      assert(vectors.size >= 12, vectors.map(_.name).mkString("\n"))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      vectors.foreach { v =>
        assertEquals(lean(ObligationName.Example(v.of, v.at)), Some(ObligationStatus.Shown), v.name)
        assertEquals(lean(ObligationName.ExampleOpposite(v.of, v.at)), Some(ObligationStatus.NotShown), v.name)
      }
    }
  }
