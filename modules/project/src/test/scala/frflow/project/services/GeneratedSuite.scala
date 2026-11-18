package frflow.project.services

import cats.effect.IO
import cats.syntax.all.*
import frflow.decision.content.Sha
import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import frflow.eval.agree.{AgreeExamples, AgreeModel}
import frflow.eval.prices.{CounterExamples, CounterModel, PricesExamples, PricesModel, RatesExamples, RatesModel}
import frflow.project.Projects
import scala.annotation.experimental
import scala.concurrent.duration.*

/** What FrFlow generates for each model, fixed: the text of every Rocq module, and the content of every node (the
  * text a decision signs). A change to the compiler from a class to Rocq that is meant to leave both as they are
  * (a refactoring of the printers, of the lowering, of the reading of a class) is held to that here, with no run
  * of Rocq. A change that is meant to move one says so by the digest it gives here.
  */
@experimental class GeneratedSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 10.minutes

  private def digests(model: FrModel, written: FrFlowExamples): IO[(String, String)] =
    val examples = written.elaborated.fold(e => throw AssertionError(e.toString), identity)
    Projects.inMemory(Map.empty).flatMap(p => Projects.analysed(p, Projects.elaborated(model), examples)).map { a =>
      (Sha(a.rocq.files.map((file, text) => s"$file\n$text").mkString("\u0000")).take(16),
        Sha(a.subjects.inOrder.map(s => s"${s.id.value} ${s.content.ref}").mkString("\n")).take(16))
    }

  private val models: List[(String, FrModel, () => FrFlowExamples)] = List(
    ("links", links.links, () => links.LinksExamples()),
    ("auth", auth.knowledge, () => auth.DecisionExamples()),
    ("prices", PricesModel.model, () => PricesExamples()),
    ("counter", CounterModel.model, () => CounterExamples()),
    ("rates", RatesModel.model, () => RatesExamples()),
    ("agree", AgreeModel.model, () => AgreeExamples()))

  /** Each model's digests: of its Rocq, and of its nodes' content. */
  private val expected: Map[String, (String, String)] = Map(
    "links" -> ("36a72ae084aa9ca8", "53f4eaeeeb532e21"),
    "auth" -> ("43438775ed73d05d", "5ef1cc0961bcd7fe"),
    "prices" -> ("4a623e791825ebd0", "c55df6f055a7bc15"),
    "counter" -> ("fb5d27bb6aa4b3e0", "6ce488dd43988124"),
    "rates" -> ("1b59be6fbbfa16c8", "f74274715f6497e0"),
    "agree" -> ("4b8e3ef8dfd7c4d8", "b1f9d53f1ade8371"))

  test("the Rocq generated for each model, and the content of its nodes, are what they were") {
    models.traverse((name, model, examples) => digests(model, examples()).map(name -> _)).map { got =>
      assertEquals(got.toMap, expected, got.map((n, d) => s"\"$n\" -> (\"${d._1}\", \"${d._2}\")").mkString(",\n"))
    }
  }
