package frflow.project.rocq.clients

import ox.*
import scala.concurrent.duration.*

/** Programs in which something fails or is cancelled: each catches what its scope gives and answers a number,
  * the same on the JVM and in Rocq (`OxRunSuite`).
  */
object Failures:
  /** A fork the scope waits for throws after the body ended: the scope throws what it threw. */
  def userForkThrows(): Int =
    try supervised { val _ = forkUser(throw IllegalStateException("boom")); 1 }
    catch case _: IllegalStateException => 2

  /** A fork that throws, joined: the scope throws what the fork threw. */
  def joinedForkThrows(): Int =
    try supervised { fork[Int](throw IllegalStateException("boom")).join() }
    catch case _: IllegalStateException => 2

  /** The body throws while a fork sleeps: the fork is interrupted, and the scope throws what the body threw. */
  def bodyThrows(): Int =
    try supervised { val _ = fork(forever(sleep(1.milli))); throw IllegalArgumentException("body") }
    catch case _: IllegalArgumentException => 3

  /** The body ends while a fork still runs: the fork is interrupted, the body's value is the scope's. */
  def daemonInterrupted(): Int = supervised { val _ = fork(forever(sleep(1.milli))); 4 }

  /** A fork not supervised throws: its `join` throws that, and the scope does not end. */
  def unsupervisedThrows(): Int = unsupervised {
    val f = forkUnsupervised[Int](throw IllegalStateException("boom"))
    try f.join()
    catch case _: IllegalStateException => 5
  }

  /** A fork cancelled: `cancel` gives the interrupt that ended it. */
  def cancelled(): Int = supervised {
    val f = forkCancellable[Int](forever(sleep(1.milli)))
    f.cancel() match
      case Left(_: InterruptedException) => 6
      case Left(_)                       => 60
      case Right(_)                      => 61
  }

  /** A fork that ends with an application error: the scope gives it. */
  def applicationError(): Int =
    val r: Either[Int, String] = supervisedError(EitherMode[Int]()) {
      val _ = forkUserError(Left(7))
      Right("done")
    }
    r.fold(identity, _ => 70)
