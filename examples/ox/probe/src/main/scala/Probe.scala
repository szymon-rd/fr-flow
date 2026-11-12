import ox.*
import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger, AtomicReference}
import java.util.concurrent.{CompletableFuture, TimeUnit, TimeoutException}

/** Two behaviours of Ox 1.1.0 predicted from its sources, run. */
object Probe:
  /** A fork of the OUTER scope is handed the INNER scope's capability and forks into it as the inner scope ends. */
  def leak(rounds: Int): (Int, Int, Int) =
    val leaks = new AtomicInteger(0)
    val refused = new AtomicInteger(0)
    val started = new AtomicInteger(0)
    for _ <- 1 to rounds do
      val innerCompleted = new AtomicBoolean(false)
      val handed = new AtomicReference[OxUnsupervised](null)
      val done = new CompletableFuture[Unit]()
      supervised {
        forkUser {
          while handed.get() == null do Thread.onSpinWait()
          try
            forkUnsupervised {
              started.incrementAndGet()
              try
                Thread.sleep(20)
                // not interrupted, still running: has the scope this is a fork of completed?
                if innerCompleted.get() then leaks.incrementAndGet()
              catch case _: InterruptedException => ()
              finally done.complete(())
            }(using handed.get())
          catch
            case _: IllegalStateException => refused.incrementAndGet(); done.complete(())
        }
        unsupervised {
          handed.set(summon[OxUnsupervised])
        }
        innerCompleted.set(true)
        done.get()
      }
    (leaks.get(), refused.get(), started.get())

  /** A fork cancelled by its scope's end, joined from outside the scope. */
  def joinOutside(): String =
    val f: Fork[Unit] = supervised { fork { Thread.sleep(3_600_000) } }
    val joined = CompletableFuture.supplyAsync(() => { f.join(); "returned" })
    try joined.get(5, TimeUnit.SECONDS)
    catch
      case _: TimeoutException => "still blocked after 5 seconds"
      case e: Throwable        => s"threw ${e.getCause}"

  def main(args: Array[String]): Unit =
    val rounds = args.headOption.map(_.toInt).getOrElse(20000)
    val (leaks, refused, started) = leak(rounds)
    println(s"leak: rounds=$rounds forks-started=$started refused=$refused ran-uninterrupted-after-their-scope-completed=$leaks")
    println(s"join outside the scope: ${joinOutside()}")
    System.exit(0)
