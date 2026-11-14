package frflow.project.rocq.clients

import java.util.concurrent.atomic.AtomicBoolean
import ox.*
import scala.concurrent.duration.*

/** Programs that observe a law of a scope: each answers what it saw once a scope had ended, a digit for each
  * thing that must have happened by then. The JVM and the meaning in Rocq must see the same (`OxRunSuite`).
  */
object Observed:
  private def seen(flags: AtomicBoolean*): Int = flags.foldLeft(0)((n, f) => n * 10 + (if f.get() then 1 else 0))

  /** A fork that runs until it is interrupted, and then says so. */
  private def untilInterrupted(said: AtomicBoolean): Unit =
    try forever(sleep(1.milli))
    catch case e: InterruptedException => { said.set(true); throw e }

  /** A scope ends after the forks it waits for: each has finished when `supervised` returns. */
  def waitsForUserForks(): Int =
    val (a, b, c) = (AtomicBoolean(false), AtomicBoolean(false), AtomicBoolean(false))
    supervised {
      val _ = forkUser { sleep(1.milli); a.set(true) }
      val _ = forkUser { sleep(2.millis); b.set(true) }
      val _ = forkUser(c.set(true))
    }
    seen(a, b, c)

  /** A scope that ends interrupts the forks still running, and returns after they have ended. */
  def interruptsAndWaits(): Int =
    val (a, b) = (AtomicBoolean(false), AtomicBoolean(false))
    supervised {
      val _ = fork(untilInterrupted(a))
      val _ = fork(untilInterrupted(b))
    }
    seen(a, b)

  /** A fork that fails ends the scope: its sibling is interrupted and has ended when the scope throws. */
  def failureInterruptsSibling(): Int =
    val sibling = AtomicBoolean(false)
    val threw =
      try supervised { val _ = fork(untilInterrupted(sibling)); forkUser[Int](throw IllegalStateException("x")).join() }
      catch case _: IllegalStateException => 2
    threw * 10 + seen(sibling)

  /** A scope inside another has ended, forks and all, before the code after it runs. */
  def innerEndsFirst(): Int =
    val (inner, outer) = (AtomicBoolean(false), AtomicBoolean(false))
    supervised {
      val before = supervised { val _ = fork(untilInterrupted(inner)); seen(outer) }
      val _ = forkUser(outer.set(true))
      before * 10 + seen(inner)
    } * 10 + seen(outer)

  /** What a scope is told to do at its end is done after its forks have ended. */
  def finalizerAfterForks(): Int =
    val (fork1, atEnd) = (AtomicBoolean(false), AtomicBoolean(false))
    supervised {
      releaseAfterScope(atEnd.set(fork1.get()))
      val _ = fork(untilInterrupted(fork1))
    }
    seen(fork1, atEnd)

  /** A scope that is not supervised also interrupts its forks and waits for them. */
  def unsupervisedWaits(): Int =
    val a = AtomicBoolean(false)
    unsupervised { val _ = forkUnsupervised(untilInterrupted(a)) }
    seen(a)

  /** `cancel` returns after the fork has ended. The fork is cancelled once it runs: one cancelled before it
    * starts never runs, and which of the two happens is the scheduler's choice.
    */
  def cancelWaits(): Int =
    val (running, a) = (AtomicBoolean(false), AtomicBoolean(false))
    supervised {
      val f = forkCancellable { running.set(true); untilInterrupted(a) }
      while !running.get() do sleep(1.milli)
      val _ = f.cancel()
      seen(a)
    }
