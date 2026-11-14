package frflow.project.rocq.clients

import java.util.concurrent.TimeoutException
import ox.*
import scala.concurrent.duration.*

/** Programs with scopes inside scopes, the operators built on them, finalizers and fork locals. */
object Scopes:
  /** A scope inside a fork of another. */
  def nested(): Int = supervised {
    val a = fork(supervised(fork(1).join() + 1))
    a.join() + 40
  }

  /** Two computations side by side. */
  def parTwo(): Int =
    val (a, b) = par(1, 2)
    a + b

  /** The first of two to end, the other never ending. */
  def raceOne(): Int = raceSuccess(5, forever(sleep(1.milli)))

  /** A computation that takes too long. */
  def timedOut(): Int =
    try timeout(5.millis)(forever(sleep(1.milli)))
    catch case _: TimeoutException => 6

  /** What a scope is told to do when it ends is done after its body, the last told first. */
  def finalizers(): Int =
    var log = 1
    supervised {
      releaseAfterScope { log = log * 10 }
      releaseAfterScope { log = log + 2 }
      log = log + 4
    }
    log

  /** A resource used in a scope is released when the scope ends, and not before. */
  def resource(): Int =
    var open = 0
    val seen = supervised {
      val r = useInScope { open = open + 1; 7 }(_ => open = open - 1)
      fork(r + open).join()
    }
    seen * 10 + open

  /** A fork reads the value a fork local has where it was started. */
  def forkLocal(): Int =
    val v = ForkLocal(1)
    val inside = supervised(v.supervisedWhere(2)(fork(v.get()).join()))
    inside * 10 + v.get()
