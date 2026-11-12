package frflow.project.services

import frflow.core.name.NodeId
import frflow.eval.run.OnCode
import frflow.eval.{Desk, DeskModel}
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import frflow.testing.report.Seed
import frflow.testing.{Settings, Vectors}
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The spike's desk, checked by Rocq end to end: a service method written in direct style over a port, read into a
  * function of the port's state, is proven to answer and to store as its claims say; and what its Scala gives on
  * generated cases Rocq decides from the `def` printed.
  */
@experimental class DeskRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the service method's claims are proven of the function of the table's rows read from it".tag(Live)) {
    val e = Projects.elaborated(DeskModel.model)
    val vectors = Vectors.of(e, Desk.book, Settings(10, Seed(1)))
    Ported.run(e, vectors, Nil).map { r =>
      List("answersWhenFree", "storesWhenFree").foreach(n =>
        assertEquals(Ported.row(r, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r)}"))
      assert(vectors.nonEmpty)
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      vectors.foreach(v => assertEquals(r.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(v.of, v.at))).map(_.status), Some(ObligationStatus.Shown), v.name))
    }
  }
