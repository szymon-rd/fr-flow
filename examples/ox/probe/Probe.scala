import ox.*
import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger, AtomicReference}
import java.util.concurrent.{CompletableFuture, TimeUnit, TimeoutException}

/** Three behaviours of Ox 1.1.0 that its proof (`examples/ox/rocq`) and the reading of its sources predict, run.
  * Each uses a capability or a fork outside the scope it belongs to.
  */
object Probe:
  private final class Counts:
    val leaks, refused, started = new AtomicInteger(0)

  /** The inner scope's fork: it sleeps, and if it was not interrupted asks whether its scope has completed. */
  private def body(counts: Counts, innerCompleted: AtomicBoolean, done: CompletableFuture[Unit]): Unit =
    counts.started.incrementAndGet()
    try
      Thread.sleep(20)
      if innerCompleted.get() then counts.leaks.incrementAndGet()
    catch case _: InterruptedException => ()
    finally done.complete(())

  /** A fork of the OUTER scope waits to be handed the INNER scope's capability, and forks into it. */
  private def outsider(counts: Counts, handed: AtomicReference[OxUnsupervised], innerCompleted: AtomicBoolean,
      done: CompletableFuture[Unit])(using Ox): Unit =
    forkUser {
      while handed.get() == null do Thread.onSpinWait()
      try forkUnsupervised(body(counts, innerCompleted, done))(using handed.get()).discard
      catch case _: IllegalStateException => counts.refused.incrementAndGet(); done.complete(())
    }.discard

  /** One round: the inner scope hands out its capability as it ends. */
  private def round(counts: Counts): Unit =
    val innerCompleted = new AtomicBoolean(false)
    val handed = new AtomicReference[OxUnsupervised](null)
    val done = new CompletableFuture[Unit]()
    supervised {
      outsider(counts, handed, innerCompleted, done)
      unsupervised(handed.set(summon[OxUnsupervised]))
      innerCompleted.set(true)
      done.get()
    }

  /** A fork cancelled by its scope's end, joined from outside the scope. */
  private def joinOutside(): String =
    val f: Fork[Unit] = supervised(fork(Thread.sleep(3_600_000)))
    val joined = CompletableFuture.supplyAsync(() => { f.join(); "returned" })
    try joined.get(5, TimeUnit.SECONDS)
    catch
      case _: TimeoutException => "still blocked after 5 seconds"
      case e: Throwable        => s"threw ${e.getCause}"

  /** A thread outside every scope, handed the capability, calls `forkUser`: was it refused? */
  private def refusedOutside(ox: Ox): Boolean =
    val refused = new AtomicBoolean(false)
    val outside = new Thread(() =>
      try forkUser(())(using ox).discard
      catch case _: IllegalStateException => refused.set(true))
    outside.start()
    outside.join()
    refused.get()

  /** `forkUser` counts the fork before `startThread` can refuse it: does the scope end once its body has? */
  private def countOff(): String =
    val scope = CompletableFuture.supplyAsync(() =>
      supervised(s"body returned (the outside forkUser was refused: ${refusedOutside(summon[Ox])})"))
    try s"supervised returned: ${scope.get(5, TimeUnit.SECONDS)}"
    catch
      case _: TimeoutException => "supervised still blocked 5 seconds after its body returned"
      case e: Throwable        => s"threw ${e.getCause}"

  def main(args: Array[String]): Unit =
    val rounds = args.headOption.map(_.toInt).getOrElse(20000)
    val c = new Counts
    (1 to rounds).foreach(_ => round(c))
    println(s"leak: rounds=$rounds forks-started=${c.started.get()} refused=${c.refused.get()} " +
      s"ran-uninterrupted-after-their-scope-completed=${c.leaks.get()}")
    println(s"join outside the scope: ${joinOutside()}")
    println(s"a refused user fork: ${countOff()}")
    System.exit(0)
