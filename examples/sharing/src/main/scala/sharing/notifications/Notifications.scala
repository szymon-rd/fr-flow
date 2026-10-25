package sharing.notifications

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.store.LibraryModel
import sharing.store.LibraryStore.store
import sharing.time.Run.{after, events}

/** Notifications: a change that concerns someone puts a notice of it in the outbox, in the same save as the change;
  * delivery sends the outbox to the mail server, a notice leaving the outbox only once the mail server has it. The mail
  * server delivers a notice once (its event is its id), so a notice sent again after a failure is not delivered twice.
  */
trait Notifications:
  /** The library with notices of a change, made by `request` and logged as `entry`, added to its outbox; `before`: the
    * library the request was made on.
    */
  def announce(library: Library, before: Library, request: Request, entry: Entry): Library

/** The mail server, as proven code sees it: it takes a notice to deliver. */
trait Mailer:
  def send(notice: Term[Notice]): Flow[Unit]

/** The mail server as the proofs see it: the notices delivered, each once, oldest first. */
object MailerModel extends Mailer, StateModel[List[Notice]]:
  def send(notice: Term[Notice]) = state.update(ns => ns.contains(notice).fold(ns, ns ++ List(notice)))

/** The mail server of the project's own: it keeps what it delivered, in memory. Tested against MailerModel. */
final class MemoryMailer(start: List[Notice] = Nil) extends Mailer:
  private val held = java.util.concurrent.atomic.AtomicReference(start)
  def delivered: List[Notice] = held.get
  def send(notice: Term[Notice]) = Flow.effect(notice)(n => held.updateAndGet(ns => if ns.contains(n) then ns else ns :+ n))

object Notifications:
  import Demo.*

  val announce = Param[(Library, Library, Request, Entry) => Library]("announce", "the library with notices of a change added to its outbox")

  val mailer: Boundary[Mailer] = Boundary.failing[Mailer]("mailer", "the mail server the service sends notices to; it may be down")(
    Failure.MailerUnavailable: Term[Failure])

  val mailerKept = Node.assumption(mailer)(MailerModel)("MailerKept",
    "The mail server delivers a notice it is given, and one it has already delivered is not delivered again; any call may fail because it is down, and then delivers nothing.",
    why = "Q13: notices are delivered at least once and never twice for one event: the outbox sends again after a failure, and the mail server keeps the notices it has delivered, by their event, so the second is dropped. An outside mail server would be checked against this model; MemoryMailer, the service's own, is tested against it.",
    idea = "Notifications")
    .implementedBy(ns => MemoryMailer(ns), _.delivered)

  /** The notices a change made by a request tells of, logged as `e`, on the library `lib` it was made on: the person
    * invited; the person who sent an invitation now accepted; the owner of a document asked for; the person whose request
    * was approved or declined. Other changes tell nobody.
    */
  private def nobody: Term[List[Notice]] = List.empty[Notice]
  val noticesOf = define { (lib: Term[Library], r: Term[Request], e: Term[Entry]) =>
    r.on[Request.Access]((_, _) => nobody)
      .on[Request.Share]((_, _, _, _, _) => nobody)
      .on[Request.Unshare]((_, _, _) => nobody)
      .on[Request.Move]((_, _, _) => nobody)
      .on[Request.Invite]((_, to, _, _) => List(Notice(to, Subject[Subject.Logged](e))))
      .on[Request.Accept]((p, what) =>
        lib.invitations.filter(i => i.to === p && i.what === what).map(i => Notice(i.by, Subject[Subject.Logged](e))))
      .on[Request.Withdraw]((_, _, _) => nobody)
      .on[Request.Trash]((_, _) => nobody)
      .on[Request.Restore]((_, _) => nobody)
      .on[Request.Ask]((_, d, _) => lib.documents.filter(doc => doc.id === d).map(doc => Notice(doc.owner, Subject[Subject.Logged](e))))
      .on[Request.Approve]((_, p, _) => List(Notice(p, Subject[Subject.Logged](e))))
      .on[Request.Decline]((_, p, _) => List(Notice(p, Subject[Subject.Logged](e))))
      .on[Request.Transfer]((_, _, to) => List(Notice(to, Subject[Subject.Logged](e))))
  }

  /** The branch: what a notice is. Its parts are announcing and delivery; that each notice is delivered once is the
    * mail server's (MailerKept).
    */
  val noticesFollowChanges = Node.claim("NoticesFollowChanges",
    "A notice is sent only of a change already kept: at every moment, every notice of a logged change, in the outbox or delivered, is of an entry in the log. A notice leaves the outbox only once the mail server has it, and the mail server has each notice once, so a person is told of each event at least once and never twice.",
    why = "Q13: invitations, accepted invitations, access requests and their answers, and transfers are notified, through an outbox, retried until delivered, at least once and never twice for one event. Putting the notice in the outbox in the save that makes the change orders them (assertion 5 of the time design): the change is kept before anyone is told of it. Shares ending within a day are not notified yet.",
    idea = "Notifications"
  )((after(events).library.outbox ++ after(events).mailbox).forall(n => n.about
      .on[Subject.Logged](e => after(events).library.log.contains(e))
      .on[Subject.Reminder](_ => True)
      .on[Subject.Lapsed](_ => True)) &&
    after(events).mailbox.forall(n => after(events).mailbox.filter(m => m === n).length === 1))
    .under(accessFollowsShares)

  private val catInvitedBy = Request.Invite(ann, cat, Target.Doc(plan), Level.View)
  private val entry = Entry(0, now, Change.Made(catInvitedBy))

  val announceContract = Node.contract(announce)("AnnounceContract",
    "Announcing a change adds, at the end of the outbox, a notice of its entry to each person it tells, as the library before the change says who: the person invited; whoever sent an invitation now accepted; the owner of a document asked for; the person whose request was approved or declined; the new owner of a document. Nothing else changes.",
    why = "Q13: what is notified and to whom. Who sent an invitation, and who owns a document, are read from the library the request was made on.",
    idea = "Notifications"
  )((lib, before, r, e, result) => result === lib.copy((outbox = lib.outbox ++ noticesOf(before, r, e))))
    .under(noticesFollowChanges, sharing.audit.Audit.auditTrail, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)
    .examples()(
      expect(library, library, catInvitedBy, entry, library.copy(outbox = List(Notice(cat, Subject.Logged(entry)))), "Cat is told of her invitation"),
      expect(library, library, Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None), entry, library,
        "a share tells nobody"),
      reject(library, library, catInvitedBy, entry, library, "an invitation is never kept from the person invited"))

  val announceCode = define { (lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
    lib.copy((outbox = lib.outbox ++ noticesOf(before, r, e)))
  }

  // ---------------------------------------------------------------------------
  // delivery: the outbox sent to the mail server, retried
  // ---------------------------------------------------------------------------

  /** How a notice is tried at the mail server: three tries, a second and then two seconds apart. */
  val retrying: Schedule = Schedule.exponential(1, retries = 2)

  val deliver = Param[() => Flow[Unit]]("deliver", "a run of delivery: the oldest notice in the outbox sent to the mail server")

  private val told = Notice(cat, Subject.Logged(entry))
  private def at(outbox: List[Notice], delivered: List[Notice], now: BigInt = now) =
    World(LibraryModel -> library.copy(outbox = outbox), MailerModel -> delivered, ClockModel -> ClockState(now, Nil))

  val deliveryJob = Node.contract(deliver)("DeliveryJob",
    "A run of delivery sends the oldest notice in the outbox to the mail server, trying three times, a second and then two seconds apart; once the mail server has it, it leaves the outbox. A run that fails leaves the outbox as it was, so the notice is sent again at the next run. Nothing else in the library changes.",
    why = "Q13: at least once, through an outbox, retried with a schedule. A notice the mail server took whose removal from the outbox then failed is sent again and dropped by the mail server (MailerKept): never twice.",
    idea = "Notifications"
  )((result, before, after) =>
    before(LibraryModel).outbox.take(1).forall(n => after(MailerModel).contains(n) &&
      after(LibraryModel) === before(LibraryModel).copy((outbox = before(LibraryModel).outbox.filterNot(m => m === n)))) &&
    (before(LibraryModel).outbox.isEmpty ==> (after(LibraryModel) === before(LibraryModel))))
    .onFailure[Failure]((e, before, after) => after(LibraryModel) === before(LibraryModel))
    .under(noticesFollowChanges)
    .examples()(
      expect(at(List(told), Nil), (), at(Nil, List(told)), "Cat's notice delivered"),
      expect(at(List(told), Nil).failing(false, true), (), at(Nil, List(told), now + 1), "the mail server was down once: delivered a second later"),
      expect(at(List(told), Nil).failing(false, true, true, true), Failed(Failure.MailerUnavailable), at(List(told), Nil, now + 3),
        "down three times: the notice stays in the outbox"),
      expect(at(List(told), Nil).failing(false, false, true), Failed(Failure.StoreUnavailable), at(List(told), List(told)),
        "delivered, but the store failed: the notice stays, to be sent again (and dropped by the mail server)"),
      expect(at(List(told), List(told)), (), at(Nil, List(told)), "sent again after that: not delivered twice"),
      reject(at(List(told), Nil).failing(false, true, true, true), Failed(Failure.MailerUnavailable), at(Nil, Nil, now + 3),
        "a notice never leaves the outbox undelivered"))

  /** One run: the outbox read, its oldest notice sent with retries, then taken out of the outbox. DeliveryJob is proven of
    * it, on the store's, the mail server's and the clock's models.
    */
  def delivery: Flow[Unit] =
    for
      lib <- store.load
      _   <- lib.outbox.take(1).traverse_(n =>
        mailer.send(n).retry[Failure](retrying) *> store.load.flatMap(l => store.save(l.copy((outbox = l.outbox.filterNot(m => m === n))))))
    yield ()

  /** Delivery every ten seconds, run in the server. */
  val schedule: Every = Flow.every(10)(delivery)
