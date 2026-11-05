package frflow.testing.examples

import frflow.dsl.example.FrFlowExamples
import sbt.testing.{EventHandler, Logger, Status, Task, TaskDef}
import scala.util.{Failure, Success, Try}

/** One class of examples: made, then each example checked and reported in the order written. */
final class ExamplesTask(task: TaskDef, loader: ClassLoader) extends Task:
  def tags(): Array[String] = Array.empty
  def taskDef(): TaskDef = task

  def execute(handler: EventHandler, loggers: Array[Logger]): Array[Task] =
    made match
      case Success(written) => Verdicts.of(written).foreach((name, v) => report(handler, loggers, name, v))
      case Failure(e)       =>
        handler.handle(NotMade(task, e))
        loggers.foreach(_.error(s"${task.fullyQualifiedName()}: not made: $e"))
    Array.empty[Task]

  private def made: Try[FrFlowExamples] = Try(Class.forName(task.fullyQualifiedName(), true, loader)
    .getDeclaredConstructor().newInstance()).flatMap {
    case w: FrFlowExamples => Success(w)
    case other             => Failure(IllegalArgumentException(s"${other.getClass.getName} writes no examples"))
  }

  private def report(handler: EventHandler, loggers: Array[Logger], name: String, v: Verdict): Unit =
    val event = ExampleEvent(task, name, v, 0)
    handler.handle(event)
    val line = s"${task.fullyQualifiedName()}: $name: ${ExampleEvent.said(v)}"
    event.status() match
      case Status.Success => loggers.foreach(_.info(s"+ $line"))
      case Status.Skipped => loggers.foreach(_.info(s"~ $line"))
      case _              => loggers.foreach(_.error(s"==> X $line"))

