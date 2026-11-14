import ox.*
import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger}

/** Whether a scope of Ox 1.1.0 can complete with a fork of its own still running, every fork made inside the
  * scope: nothing here hands a capability out. The closing loop ends when `threads.isEmpty` answers `true`, and
  * `ConcurrentHashMap`'s `isEmpty` sums counters that other threads are changing (its documentation: "not for
  * program control"). A fork that starts a short-lived fork adds one to a counter of its own; the short-lived
  * fork, ending, takes one from another. A sum that reads the first before and the second after is one short.
  *
  *   sbt "runMain EmptyProbe 200000 4"
  */
object EmptyProbe:
  private val leaks, lingered, interrupted, children = new AtomicInteger(0)

  /** A fork that forks short-lived forks until the scope refuses (it has begun to close), and then lingers: the
    * scope is to interrupt it and wait for it, so it should never find the scope completed.
    */
  private def spawner(completed: AtomicBoolean)(using Ox): Unit =
    fork {
      try
        while true do
          fork(()).discard
          children.incrementAndGet()
      catch case _: IllegalStateException => ()
      lingered.incrementAndGet()
      try
        Thread.sleep(30)
        if completed.get() then leaks.incrementAndGet()
      catch case _: InterruptedException => interrupted.incrementAndGet()
    }.discard

  private def round(spawners: Int): Unit =
    val completed = new AtomicBoolean(false)
    supervised {
      (1 to spawners).foreach(_ => spawner(completed))
      Thread.onSpinWait()
    }
    completed.set(true)

  def main(args: Array[String]): Unit =
    val rounds = args.headOption.map(_.toInt).getOrElse(20000)
    val spawners = args.lift(1).map(_.toInt).getOrElse(4)
    val start = System.nanoTime()
    (1 to rounds).foreach(_ => round(spawners))
    Thread.sleep(200)
    println(s"isEmpty: rounds=$rounds spawners=$spawners short-lived-forks=${children.get()} " +
      s"lingered=${lingered.get()} interrupted=${interrupted.get()} " +
      s"ran-uninterrupted-after-their-scope-completed=${leaks.get()} seconds=${(System.nanoTime() - start) / 1000000000}")
    System.exit(0)
