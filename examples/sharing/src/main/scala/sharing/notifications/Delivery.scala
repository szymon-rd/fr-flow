package sharing.notifications

import frflow.*
import sharing.domain.*
import sharing.store.LibraryStore

/** One run of delivery: a connection taken from the pool and given back whatever happens; the outbox read, and the
  * oldest notice of each person in it delivered, four at once, the whole given half a minute: past it, the sends are
  * cancelled, to go on at the next run. Each notice is tried three times, a second and then two seconds apart; once
  * the mail server has it, it is taken out of the outbox in one transaction. Its failures end with it: one notice
  * failing never cancels another's delivery.
  */
object Delivery:
  private val done: Term[Unit] = ()
  private val waits: List[BigInt] = List(1, 2)
  private val atOnce = 4
  /** How long a run's sends may take, in seconds. */
  val limit: BigInt = 30

  def run: Flow[Unit] =
    Flow.bracket[Failure, Unit, Unit](Flow.step(Pool.take))(_ =>
      sendAll.race(Flow.step(Clock.sleep(limit))).void)(_ => Flow.step(Pool.give))

  /** The sends, four at once: the branches the interleavings run at once. */
  private[sharing] def sendAll: Flow[Unit] =
    for
      lib <- LibraryStore.load
      _   <- Flow.parCollectN(atOnce)(Notifications.firstOfEach(lib.outbox))(n => deliverOne(n))
    yield done

  private def deliverOne(n: Term[Notice]): Flow[Unit] =
    for
      sent <- Flow.retry[Failure, Unit](Clock.sleep, waits)(Flow.step(Mailer.send(n))).as(done).attempt[Failure]
      _    <- Flow.when(sent.isRight)(taken(n).as(done).attempt[Failure].void)
    yield done

  /** The notice taken out of the outbox, in one transaction. */
  private def taken(n: Term[Notice]): Flow[Unit] =
    LibraryStore.load.flatMap(l => Flow.step(LibraryStore.save(l.updated(_.outbox, l.outbox.filter(m => m =!= n)))))
      .atomically
