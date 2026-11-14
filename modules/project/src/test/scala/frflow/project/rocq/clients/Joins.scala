package frflow.project.rocq.clients

import ox.*

/** Programs that fork and join: what each gives on the JVM is what its meaning, run in Rocq, must give
  * (`OxRunSuite`).
  */
object Joins:
  /** No thread: a value. */
  def plain(): Int = 1 + 2

  /** A scope with nothing forked. */
  def scoped(): Int = supervised(40 + 2)

  /** One fork, joined. */
  def forkJoin(): Int = supervised {
    val f = fork(1 + 2)
    f.join()
  }

  /** Two forks, both joined. */
  def two(): Int = supervised {
    val a = fork(20)
    val b = fork(22)
    a.join() + b.join()
  }
