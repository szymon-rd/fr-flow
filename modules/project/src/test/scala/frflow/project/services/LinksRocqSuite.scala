package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, Result}
import links.LinksExamples
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The link shortener (`examples/links`), checked by Rocq end to end: the class given for the shortener is proven
  * to meet each claim on its members; its examples hold on the code, and Rocq shows each by running the code on the
  * values it gives; every condition of a claim is shown possible.
  */
@experimental class LinksRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("every claim of the shortener is proven, each condition can hold, and Rocq shows its examples".tag(Live)) {
    val examples = LinksExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(links.links), examples, Ported.proofs("links", "Shortener")).map { r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      val whole = r.wholeCheck.toList.flatMap(_.results)
      examples.foreach { e =>
        def status(name: ObligationName) = whole.find(_.name == name).map(_.status)
        assertEquals(status(ObligationName.Example(e.of, e.at)), Some(ObligationStatus.Shown), e.name)
        assertEquals(status(ObligationName.ExampleOpposite(e.of, e.at)), Some(ObligationStatus.NotShown), e.name)
      }
      val open = whole.collect { case Result(n @ ObligationName.Satisfiable(_, _), status, _)
        if status != ObligationStatus.Proven => n }
      assertEquals(open, Nil)
    }
  }
