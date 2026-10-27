package frflow.testing.examples

import sbt.testing.{Event, Fingerprint, OptionalThrowable, Selector, Status, SuiteSelector, TaskDef}

/** A class that could not be made: an error of the whole class. */
final case class NotMade(task: TaskDef, cause: Throwable) extends Event:
  def fullyQualifiedName(): String = task.fullyQualifiedName()
  def fingerprint(): Fingerprint = task.fingerprint()
  def selector(): Selector = SuiteSelector()
  def status(): Status = Status.Error
  def throwable(): OptionalThrowable = OptionalThrowable(cause)
  def duration(): Long = 0
