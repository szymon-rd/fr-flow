package frflow.testing.examples

import sbt.testing.{Runner, Task, TaskDef}

/** One run of the examples' classes sbt found: a task per class. */
final class ExamplesRunner(argsGiven: Array[String], remoteArgsGiven: Array[String], loader: ClassLoader)
    extends Runner:
  def args(): Array[String] = argsGiven
  def remoteArgs(): Array[String] = remoteArgsGiven
  def tasks(defs: Array[TaskDef]): Array[Task] = defs.map(d => ExamplesTask(d, loader))
  def done(): String = ""
