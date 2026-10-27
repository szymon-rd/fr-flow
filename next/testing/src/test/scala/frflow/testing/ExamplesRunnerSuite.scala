package frflow.testing

import frflow.*
import frflow.eval.run.OnCode
import frflow.testing.examples.{ExamplesFramework, Verdict, Verdicts}
import sbt.testing.{Event, EventHandler, Logger, Status, SuiteSelector, TaskDef, TestSelector}
import scala.collection.mutable.ListBuffer

/** The examples' runner: each example of a class run against the code as `sbt test` runs it, in the order written,
  * holding, failing, or checked in Lean only (owner §18: examples are ordinary tests beside the model).
  */
class ExamplesRunnerSuite extends munit.FunSuite:
  private def verdicts(written: FrFlowExamples): List[(String, Verdict)] = Verdicts.of(written)

  test("every example of rooms and auth holds of the code, in the order written") {
    assertEquals(verdicts(rooms.GrantedExamples()).map(_._2), List.fill(2)(Verdict.Ran(OnCode.Holds)))
    assertEquals(verdicts(auth.DecisionExamples()).map(_._1).headOption,
      Some("Alice's token and a grant for /a: she gets in"))
    assert(verdicts(auth.DecisionExamples()).forall(_._2 == Verdict.Ran(OnCode.Holds)))
  }

  test("crm's example reads the history it does not give: no Scala value, checked in Lean only, so skipped") {
    val run = events(classOf[crm.ExpectationsExamples].getName)
    assertEquals(run.map(_.status()), List(Status.Skipped))
  }

  test("sbt runs a class of examples: one event per example, named by it; a failing one fails") {
    val run = events(classOf[ShelfExamples].getName)
    assertEquals(run.map(e => (e.selector(), e.status())), List(
      TestSelector("a long book is picked, a short one left") -> Status.Success,
      TestSelector("an empty shelf gives nothing") -> Status.Success))
    val wrong = new FrFlowExamples(Shelf.kb):
      example("a short book is picked", Shelf.minPages := BigInt(100)):
        Shelf.picks(List(Shelf.Book("Short", 10)), 1) is List(Shelf.Book("Short", 10))
    assertEquals(verdicts(wrong).map(_._2), List(Verdict.Ran(OnCode.Fails)))
  }

  test("a class that cannot be found or made is an error of the class") {
    assertEquals(events("frflow.testing.NoSuchExamples").map(e => (e.selector(), e.status())),
      List(SuiteSelector() -> Status.Error))
  }

  /** The events the framework's task for `name` sends, as sbt would collect them. */
  private def events(name: String): List[Event] =
    val framework = ExamplesFramework()
    val runner = framework.runner(Array.empty, Array.empty, getClass.getClassLoader)
    val seen = ListBuffer.empty[Event]
    val handler: EventHandler = e => seen += e
    runner.tasks(Array(TaskDef(name, ExamplesFramework.Written, false, Array(SuiteSelector()))))
      .foreach(_.execute(handler, Array.empty[Logger]))
    seen.toList
