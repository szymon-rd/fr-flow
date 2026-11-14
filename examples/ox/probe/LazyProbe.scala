import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger

/** What a thread does that reads a `lazy val` another thread is evaluating and is interrupted while it waits, and
  * what a second read gives after an evaluation that threw: of a member of an object, and of one written inside
  * a method. `FrFlow/Threads/Jdk.v` states both as the contract of `LazyEnter`.
  *
  *   cd examples/ox/probe && sbt "runMain LazyProbe"
  */
object LazyHolder:
  val started = CountDownLatch(1)
  val attempts = AtomicInteger(0)
  lazy val slow: Int = LazyProbe.slowly(started)
  lazy val failing: Int = LazyProbe.secondTime(attempts.incrementAndGet())

object LazyProbe:
  def slowly(started: CountDownLatch): Int = { started.countDown(); Thread.sleep(1500); 42 }
  def secondTime(attempt: Int): Int = if attempt == 1 then throw IllegalStateException("first") else 7

  def reading(read: => Int): String =
    try s"value $read (interrupted: ${Thread.currentThread().isInterrupted})"
    catch case e: Throwable => s"threw ${e.getClass.getName}"

  /** A second thread reads while the first evaluates, and is interrupted: what its read gave. */
  def waiter(started: CountDownLatch)(read: => Int): String =
    val first = Thread.ofVirtual().start(() => { val _ = read })
    started.await()
    val outcome = java.util.concurrent.atomic.AtomicReference("none")
    val second = Thread.ofPlatform().start(() => outcome.set(reading(read)))
    Thread.sleep(200)
    second.interrupt()
    second.join()
    first.join()
    outcome.get()

  def inMethod(): Unit =
    val started = CountDownLatch(1)
    lazy val slow: Int = slowly(started)
    println(s"in a method, interrupted while waiting: ${waiter(started)(slow)}")
    val attempts = AtomicInteger(0)
    lazy val failing: Int = secondTime(attempts.incrementAndGet())
    println(s"in a method, after a failed evaluation: ${reading(failing)}, then ${reading(failing)}")

  def main(args: Array[String]): Unit =
    println(s"a member, interrupted while waiting: ${waiter(LazyHolder.started)(LazyHolder.slow)}")
    println(s"a member, after a failed evaluation: ${reading(LazyHolder.failing)}, then ${reading(LazyHolder.failing)}")
    inMethod()
