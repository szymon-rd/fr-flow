package frflow.testing.examples

import frflow.eval.run.OnCode
import sbt.testing.{Event, Fingerprint, OptionalThrowable, Selector, Status, TaskDef, TestSelector}

/** One example's outcome as sbt counts it: holding passes, failing fails; one with no Scala value or about
  * Declarations is skipped here, as it is checked against the claims in Lean only; one the code could not evaluate
  * otherwise (a fault of the code or its wiring), or not read, is an error.
  */
final case class ExampleEvent(task: TaskDef, name: String, verdict: Verdict, millis: Long) extends Event:
  def fullyQualifiedName(): String = task.fullyQualifiedName()
  def fingerprint(): Fingerprint = task.fingerprint()
  def selector(): Selector = TestSelector(name)
  def duration(): Long = millis
  def throwable(): OptionalThrowable = status() match
    case Status.Failure | Status.Error => OptionalThrowable(AssertionError(s"$name: ${ExampleEvent.said(verdict)}"))
    case _                             => OptionalThrowable()

  def status(): Status = verdict match
    case Verdict.Ran(OnCode.Holds) => Status.Success
    case Verdict.Ran(OnCode.Fails) => Status.Failure
    case Verdict.LeanOnly(_)       => Status.Skipped
    case _                         => Status.Error

object ExampleEvent:
  /** What sbt prints beside the example's name. */
  def said(v: Verdict): String = v match
    case Verdict.Ran(OnCode.Holds)             => "holds of the code"
    case Verdict.Ran(OnCode.Fails)             => "the code does not meet it"
    case Verdict.Ran(other)                    => s"the code could not evaluate it ($other): a fault of its wiring"
    case Verdict.LeanOnly(OnCode.Abstract(ds)) =>
      s"about ${ds.map(_.value).mkString(", ")}, which have no code: checked against the claims in Lean only"
    case Verdict.LeanOnly(other)               => s"no Scala value ($other): checked against the claims in Lean only"
    case Verdict.NotRead(es)                   => s"not read: ${es.mkString("; ")}"
