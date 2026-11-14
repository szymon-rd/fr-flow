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
  private val set = ConcurrentHashMap.newKeySet[Object]()
  private val stop = new AtomicBoolean(false)
  private val asked, wrong, moved = new AtomicLong(0)

  private def thread(body: => Unit): Thread =
    val t = new Thread(() => body)
    t.start()
    t

  /** One thread adds elements and hands each to another, which removes it. */
  private def pair(): List[Thread] =
    val handed = new ConcurrentLinkedQueue[Object]()
    def add(): Unit =
      val k = new Object
      set.add(k)
      val _ = handed.offer(k)
    def remove(): Unit = Option(handed.poll()).foreach { k =>
      set.remove(k)
      moved.incrementAndGet() }
    List(thread(while !stop.get() do add()), thread(while !stop.get() do remove()))

  /** Asks `isEmpty` until told to stop: how often, and how often the answer was `true`. */
  private def reader(): Thread = thread {
    var n, w = 0L
    while !stop.get() do
      if set.isEmpty then w += 1
      n += 1
    asked.set(n)
    wrong.set(w) }

  def main(args: Array[String]): Unit =
    val seconds = args.headOption.map(_.toInt).getOrElse(30)
    val pairs = args.lift(1).map(_.toInt).getOrElse(2)
    set.add(new Object) // stays for the whole run
    val threads = reader() :: (1 to pairs).toList.flatMap(_ => pair())
    Thread.sleep(seconds * 1000L)
    stop.set(true)
    threads.foreach(_.join())
    println(s"isEmpty on a set that always holds an element: asked=${asked.get()} answered-true=${wrong.get()} " +
      s"elements-added-and-removed=${moved.get()} pairs=$pairs seconds=$seconds " +
      s"java=${System.getProperty("java.version")}")
    System.exit(0)
