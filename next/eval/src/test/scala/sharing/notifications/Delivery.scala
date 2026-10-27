package sharing.notifications

import frflow.*
import sharing.domain.*
import sharing.store.LibraryStore

/** One run of delivery: the outbox read, and the oldest notice of each person in it delivered, four at once. Each
  * notice is tried three times, a second and then two seconds apart; once the mail server has it, it is taken out of
  * the outbox in one transaction. Its failures end with it: one notice failing never cancels another's delivery.
  */
final class Delivery[F[_]](store: LibraryStore[F, Term], mailer: Mailer[F, Term], clock: Clock[F, Term])(
    using f: Flow[F]):
  private val done: Term[Unit] = ()
  private val waits: List[BigInt] = List(1, 2)
  private val atOnce = 4

  def run: F[Term[Unit]] = f.flatMap(store.load)(lib =>
    f.as(f.parCollectN(atOnce)(Notifications.firstOfEach(lib.outbox))(n => deliverOne(n)), done))

  private def deliverOne(n: Term[Notice]): F[Term[Unit]] =
    f.flatMap(f.attempt[Failure, Unit](f.as(f.retry[Failure, Unit](clock, waits)(mailer.send(n)), done)))(sent =>
      f.as(f.cond(sent.isRight)(f.void(f.attempt[Failure, Unit](f.as(taken(n), done))), f.unit),
        done))

  /** The notice taken out of the outbox, in one transaction. */
  private def taken(n: Term[Notice]): F[Unit] = f.atomically(
    f.flatMap(store.load)(l => store.save(l.updated(_.outbox, l.outbox.filter(m => m =!= n)))))
