package sharing.notifications

import frflow.*
import sharing.domain.*
import sharing.store.LibraryStore

/** One run of delivery: the outbox read, and the oldest notice of each person in it delivered, four at once. Each
  * notice is tried three times, a second and then two seconds apart; once the mail server has it, it is taken out of
  * the outbox in one transaction. Its failures end with it: one notice failing never cancels another's delivery.
  */
object Delivery:
  private val done: Term[Unit] = ()
  private val waits: List[BigInt] = List(1, 2)
  private val atOnce = 4

  def run[F[_]](using f: Flow[F]): F[Term[Unit]] = f.flatMap(LibraryStore.load)(lib =>
    f.as(f.parCollectN(atOnce)(Notifications.firstOfEach(lib.outbox))(n => deliverOne(n)), done))

  private def deliverOne[F[_]](n: Term[Notice])(using f: Flow[F]): F[Term[Unit]] =
    f.flatMap(f.attempt[Failure, Unit](f.as(f.retry[Failure, Unit](Clock.sleep, waits)(Mailer.send(n)), done)))(
      sent => f.as(f.cond(sent.isRight)(f.void(f.attempt[Failure, Unit](f.as(taken(n), done))), f.unit), done))

  /** The notice taken out of the outbox, in one transaction. */
  private def taken[F[_]](n: Term[Notice])(using f: Flow[F]): F[Unit] = f.atomically(
    f.flatMap(LibraryStore.load)(l => LibraryStore.save(l.updated(_.outbox, l.outbox.filter(m => m =!= n)))))
