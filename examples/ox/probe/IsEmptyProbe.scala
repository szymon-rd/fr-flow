import java.util.concurrent.{ConcurrentHashMap, ConcurrentLinkedQueue}
import java.util.concurrent.atomic.{AtomicBoolean, AtomicLong}

/** The JDK alone, as Ox's thread set uses it: a `ConcurrentHashMap.newKeySet()` that always holds one element;
  * other elements added by one thread and removed by another (in Ox a fork is added by the thread that starts it
  * and removes itself); and a thread that asks `isEmpty` over and over. The set is never empty: does `isEmpty`
  * ever answer `true`?
  *
  *   sbt "runMain IsEmptyProbe 30 2"
  */
object IsEmptyProbe:
  def main(args: Array[String]): Unit =
    val seconds = args.headOption.map(_.toInt).getOrElse(30)
    val pairs = args.lift(1).map(_.toInt).getOrElse(2)
    val set = ConcurrentHashMap.newKeySet[Object]()
    set.add(new Object)                                   // stays for the whole run
    val stop = new AtomicBoolean(false)
    val asked, wrong, moved = new AtomicLong(0)
    def thread(body: => Unit): Thread = { val t = new Thread(() => body); t.start(); t }
    val workers = (1 to pairs).flatMap { _ =>
      val handed = new ConcurrentLinkedQueue[Object]()
      List(thread { while !stop.get() do { val k = new Object; set.add(k); handed.offer(k) } },
        thread { while !stop.get() do { val k = handed.poll(); if k != null then { set.remove(k); moved.incrementAndGet() } } }) }
    val reader = thread {
      var n, w = 0L
      while !stop.get() do { if set.isEmpty then w += 1; n += 1 }
      asked.set(n); wrong.set(w) }
    Thread.sleep(seconds * 1000L)
    stop.set(true)
    (reader :: workers.toList).foreach(_.join())
    println(s"isEmpty on a set that always holds an element: asked=${asked.get()} answered-true=${wrong.get()} " +
      s"elements-added-and-removed=${moved.get()} pairs=$pairs seconds=$seconds java=${System.getProperty("java.version")}")
    System.exit(0)
