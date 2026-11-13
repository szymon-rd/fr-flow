package frflow.project.services

import frflow.eval.agree.{AgreeExamples, AgreeModel, AgreeSuite}
import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The Rocq FrFlow generates from a class gives what the class gives on the JVM. Each example of `AgreeExamples`
  * is a member of a class run on drawn inputs, stated as the result and the state the JVM gave: Rocq shows it by
  * running the generated definitions, and does not show its opposite. A result the class does not give is not
  * shown, and its opposite is. The classes cover each kind of Scala the compiler reads (`frflow.eval.agree`).
  */
@experimental class AgreeRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private def statuses(written: frflow.dsl.example.FrFlowExamples) =
    val examples = written.elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(AgreeModel.model), examples, Nil).map { r =>
      val whole = r.wholeCheck.toList.flatMap(_.results)
      def status(name: ObligationName) = whole.find(_.name == name).map(_.status)
      (r, examples.map(e => (e.name, status(ObligationName.Example(e.of, e.at)),
        status(ObligationName.ExampleOpposite(e.of, e.at)))))
    }

  test("every member, run by Rocq on the definitions generated from its class, gives what the JVM gives".tag(Live)) {
    statuses(AgreeExamples()).map { (r, shown) =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      assertEquals(shown.filterNot((_, is, opposite) => is.contains(ObligationStatus.Shown) &&
        opposite.contains(ObligationStatus.NotShown)), Nil)
    }
  }

  test("a result the class does not give is not shown by Rocq, and its opposite is".tag(Live)) {
    statuses(AgreeSuite.Wrong()).map { (_, shown) =>
      assertEquals(shown.filterNot((_, is, opposite) => is.contains(ObligationStatus.NotShown) &&
        opposite.contains(ObligationStatus.Shown)), Nil)
    }
  }
