package sharing.notifications

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.requests.AccessRequests
import sharing.store.LibraryModel
import sharing.store.LibraryStore.store
import sharing.time.Run.{after, events}

/** Notifications: a change that concerns someone puts a notice of it in the outbox, in the same save as the change;
  * delivery sends the outbox to the mail server, four people's notices at once, a notice leaving the outbox only once
  * the mail server has it. The mail server keeps each person's notices in the order it got them, and takes a notice
  * once (its event is its id), so a notice sent again after a failure is not delivered twice.
  */
trait Notifications:
  /** The library with notices of a change, made by `request` and logged as `entry`, added to its outbox; `before`: the
    * library the request was made on.
    */
  def announce(library: Library, before: Library, request: Request, entry: Entry): Library

/** The mail server, as proven code sees it: it takes a notice to deliver. */
trait Mailer:
  def send(notice: Term[Notice]): Flow[Unit]

/** The mail server as the proofs see it: each person's mailbox, the notices delivered to them, each once, oldest
  * first. Order is kept per person, not across people (Q17): two people's deliveries change two mailboxes.
  */
object MailerModel extends Mailer, StateModel[Map[PersonId, List[Notice]]]:
  def send(notice: Term[Notice]) = state.update(boxes => boxes.updated(notice.to, Notifications.taken(Notifications.mailbox(boxes, notice.to), notice)))

/** The mail server of the project's own: it keeps each person's mailbox, in memory. Tested against MailerModel. */
final class MemoryMailer(start: Map[PersonId, List[Notice]] = Map.empty) extends Mailer:
  private val held = java.util.concurrent.atomic.AtomicReference(start)
  def boxes: Map[PersonId, List[Notice]] = held.get
  /** Every notice delivered, person by person. */
  def delivered: List[Notice] = held.get.toList.sortBy(_._1.name).flatMap(_._2)
  def send(notice: Term[Notice]) = Flow.effect(notice)(n =>
    held.updateAndGet(m => m.updated(n.to, m.getOrElse(n.to, Nil) match { case ns if ns.contains(n) => ns; case ns => ns :+ n })))

object Notifications:
  import Demo.*

  val announce = Param[(Library, Library, Request, Entry) => Library]("the library with notices of a change added to its outbox")

  val mailer: Boundary[Mailer] = Boundary.failing[Mailer]("mailer", "the mail server the service sends notices to; it may be down")(
    Failure.MailerUnavailable: Term[Failure])

  val mailerKept = Node.assumption(mailer)(MailerModel)("The mail server delivers a notice it is given into the mailbox of the person it is to, after the ones delivered there before, and one it has already delivered is not delivered again; any call may fail because it is down, and then delivers nothing.",
    why = "Q13: notices are delivered at least once and never twice for one event: the outbox sends again after a failure, and the mail server keeps the notices it has delivered, by their event, so the second is dropped. Q17: each person's notices keep their order, two people's need not, so deliveries to two people at once commute. An outside mail server would be checked against this model; MemoryMailer, the service's own, is tested against it.",
    idea = "Notifications")
    .implementedBy(boxes => MemoryMailer(boxes), _.boxes)

  /** A person's mailbox: the notices delivered to them, oldest first. */
  val mailbox = define { (boxes: Term[Map[PersonId, List[Notice]]], p: Term[PersonId]) => boxes.getOrElse(p, List.empty[Notice]) }
  /** A mailbox after a notice is given to the mail server: the notice at the end, unless it is there already. */
  val taken = define { (ns: Term[List[Notice]], n: Term[Notice]) => ns.contains(n).fold(ns, ns ++ List(n)) }

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
      .on[Request.Ask]((_, w, _) => lib.documents.filter(doc => AccessRequests.isFor(w, doc)).map(doc => Notice(doc.owner, Subject[Subject.Logged](e))))
      .on[Request.Approve]((_, p, _) => List(Notice(p, Subject[Subject.Logged](e))))
      .on[Request.Decline]((_, p, _) => List(Notice(p, Subject[Subject.Logged](e))))
      .on[Request.Transfer]((_, _, to) => List(Notice(to, Subject[Subject.Logged](e))))
  }

  /** The branch: what a notice is. Its parts are announcing and delivery; that each notice is delivered once is the
    * mail server's (MailerKept).
    */
  val noticesFollowChanges = Node.claim("A notice is sent only of a change already kept: at every moment, every notice of a logged change waiting in the outbox is of an entry in the log. A notice leaves the outbox only once the mail server has it, and the mail server has each notice once, so a person is told of each event at least once and never twice.",
    why = "Q13: invitations, accepted invitations, access requests and their answers, transfers, and shares ending within a day are notified, through an outbox, retried until delivered, at least once and never twice for one event. Putting the notice in the outbox in the save that makes the change orders them (assertion 5 of the time design): the change is kept before anyone is told of it, and kept while the notice waits (ForgetContract); a notice delivered may outlive its entry's year.",
    idea = "Notifications"
  )(after(events).library.outbox.forall(n => n.about
      .on[Subject.Logged](e => after(events).library.log.contains(e))
      .on[Subject.Reminder](_ => True)
      .on[Subject.Lapsed](_ => True)
      .on[Subject.Ending](_ => True)) &&
    after(events).mailbox.forall(n => after(events).mailbox.filter(m => m === n).length === 1))
    .refines(accessFollowsShares)

  private val catInvitedBy = Request.Invite(ann, cat, Target.Doc(plan), Level.View)
  private val entry = Entry(0, now, Change.Made(catInvitedBy))

  val announceContract = Node.contract(announce)("Announcing a change adds, at the end of the outbox, a notice of its entry to each person it tells, as the library before the change says who: the person invited; whoever sent an invitation now accepted; the owner of a document asked for; the person whose request was approved or declined; the new owner of a document. Nothing else changes.",
    why = "Q13: what is notified and to whom. Who sent an invitation, and who owns a document, are read from the library the request was made on.",
    idea = "Notifications"
  )((lib, before, r, e, result) => result === lib.copy((outbox = lib.outbox ++ noticesOf(before, r, e))))
    .refines(noticesFollowChanges, sharing.audit.Audit.auditTrail, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)
    .examples()(
      allows(library, library, catInvitedBy, entry, library.copy(outbox = List(Notice(cat, Subject.Logged(entry)))), "Cat is told of her invitation"),
      allows(library, library, Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None), entry, library,
        "a share tells nobody"),
      forbids(library, library, catInvitedBy, entry, library, "an invitation is never kept from the person invited"))

  val announceCode = define { (lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
    lib.copy((outbox = lib.outbox ++ noticesOf(before, r, e)))
  }

  // ---------------------------------------------------------------------------
  // shares ending within a day: housekeeping tells the people they reach
  // ---------------------------------------------------------------------------

  val warn = Param[(Library, BigInt) => Library]("the library with notices of the shares ending within a day")

  /** The people a share reaches, by name: the person it is with, or the members of the team. */
  val reachedBy = define { (lib: Term[Library], s: Term[Share]) =>
    s.withWhom.on[Grantee.Person](p => List(p)).on[Grantee.Team](t => lib.teams.filter(team => team.id === t).flatMap(team => team.members))
  }
  /** The window a share's end is told of in: two minutes, the longest housekeeping goes without a run
    * (HousekeepingPeriod). A value, not the open term: the term would become an input of every definition of the run.
    */
  val window: BigInt = 120
  /** Whether a share ends a day after a moment, within the window: the run of housekeeping nearest a day before its end
    * tells of it.
    */
  val endsInADay = define { (s: Term[Share], t: Term[BigInt]) =>
    s.until.exists(u => u <= t + day && u > t + day - window)
  }
  /** The notices of the shares ending in a day, to each person each reaches. */
  val endingNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.filter(s => endsInADay(s, t)).flatMap(s => reachedBy(lib, s).map(p => Notice(p, Subject[Subject.Ending](s))))
  }

  private val bobsHourEndsInADay = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, Some(now + day - 30))

  val warnContract = Node.contract(warn)("Housekeeping tells of the shares ending within a day: at a moment, it adds at the end of the outbox a notice, to each person a share reaches, of each share whose end comes a day on, within one housekeeping period. Nothing else changes.",
    why = "Q13 as assumed: shares ending within a day are notified. Housekeeping runs every minute and never two minutes apart (HousekeepingOnTime), so a share's end falls in the window of one run or two; the mail server keeps a notice once (MailerKept), so each person is told once.",
    idea = "Notifications"
  )((lib, t, result) => result === lib.copy((outbox = lib.outbox ++ endingNotices(lib, t))))
    .refines(noticesFollowChanges)
    .examples()(
      allows(library.copy(shares = bobsHourEndsInADay :: library.shares), now,
        library.copy(shares = bobsHourEndsInADay :: library.shares, outbox = List(Notice(bob, Subject.Ending(bobsHourEndsInADay)))),
        "Bob's share ends in a day: he is told"),
      allows(library.copy(shares = bobsHourEndsInADay :: library.shares), now - 3600, library.copy(shares = bobsHourEndsInADay :: library.shares),
        "a day and an hour before: not yet"),
      forbids(library.copy(shares = bobsHourEndsInADay :: library.shares), now, library.copy(shares = bobsHourEndsInADay :: library.shares),
        "a share ending is never left untold"))

  val warnCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.copy((outbox = lib.outbox ++ endingNotices(lib, t)))
  }

  // ---------------------------------------------------------------------------
  // delivery: the outbox sent to the mail server, four people at once, retried
  // ---------------------------------------------------------------------------

  /** How a notice is tried at the mail server: three tries, a second and then two seconds apart. */
  val retrying: Schedule = Schedule.exponential(1, retries = 2)
  /** How many notices are sent at once (Q17). */
  val atOnce: Int = 4

  /** The oldest notice of each person in an outbox, in the outbox's order: what a run of delivery sends. Two of them are
    * never to the same person, so each person's notices go in order, one a run.
    */
  val firstOfEach = define { (outbox: Term[List[Notice]]) => outbox.filter(n => outbox.find(m => m.to === n.to).contains(n)) }

  val deliver = Param[() => Flow[Unit]]("a run of delivery: the oldest notice of each person in the outbox sent to the mail server")

  private val told = Notice(cat, Subject.Logged(entry))
  private val toldBob = Notice(bob, Subject.Logged(entry.copy(id = 1)))
  private val toldCatAgain = Notice(cat, Subject.Logged(entry.copy(id = 2)))
  private def boxes(ns: Notice*): Map[PersonId, List[Notice]] = ns.toList.groupBy(_.to)
  private def at(outbox: List[Notice], delivered: Map[PersonId, List[Notice]], now: BigInt = now) =
    World(LibraryModel -> library.copy(outbox = outbox), MailerModel -> delivered, ClockModel -> ClockState(now, Nil))

  val deliveryJob = Node.contract(deliver)("A run of delivery reads the outbox and sends the oldest notice of each person in it to the mail server, four at once, each tried three times, a second and then two seconds apart. A notice leaves the outbox only once the mail server has it, and only such a notice: one the mail server did not take stays, to be sent at the next run. The mailbox of each person sent to is as it was, or holds that notice too. Nothing else in the library changes. When the outbox cannot be read, nothing changes.",
    why = "Q13: at least once, through an outbox, retried with a schedule; a notice the mail server took whose removal from the outbox then failed is sent again and dropped by the mail server (MailerKept): never twice. Q17: up to four at once, order kept per person (one notice of each person a run). Each branch handles its own failures, so one person's notice failing never stops another's; the branches are proven to commute (two people's notices change two mailboxes, and leave the outbox by their own removal), and each removal is one transaction, so a request adding to the outbox meanwhile is kept (Q20).",
    idea = "Notifications"
  )((result, before, after) =>
    let(firstOfEach(before(LibraryModel).outbox))(heads =>
      after(LibraryModel) === before(LibraryModel).copy((outbox = before(LibraryModel).outbox.filter(n => after(LibraryModel).outbox.contains(n)))) &&
      before(LibraryModel).outbox.forall(n => after(LibraryModel).outbox.contains(n) ||
        (heads.contains(n) && mailbox(after(MailerModel), n.to).contains(n))) &&
      heads.forall(n => mailbox(after(MailerModel), n.to) === mailbox(before(MailerModel), n.to) ||
        mailbox(after(MailerModel), n.to) === taken(mailbox(before(MailerModel), n.to), n))))
    .onFailure[Failure]((e, before, after) => after(LibraryModel) === before(LibraryModel) && after(MailerModel) === before(MailerModel))
    .refines(noticesFollowChanges)
    .examples()(
      allows(at(List(told), Map.empty), (), at(Nil, boxes(told)), "Cat's notice delivered"),
      allows(at(List(told, toldBob, toldCatAgain), Map.empty), (), at(List(toldCatAgain), boxes(told, toldBob)),
        "Cat's first and Bob's go at once; Cat's second waits for the next run"),
      allows(at(List(told), Map.empty).failing(false, true), (), at(Nil, boxes(told), now + 1), "the mail server was down once: delivered a second later"),
      allows(at(List(told), Map.empty).failing(false, true, true, true), (), at(List(told), Map.empty, now + 3),
        "down three times: the notice stays in the outbox, for the next run"),
      allows(at(List(told), Map.empty).failing(false, false, true), (), at(List(told), boxes(told)),
        "delivered, but the store failed: the notice stays, to be sent again (and dropped by the mail server)"),
      allows(at(List(told), boxes(told)), (), at(Nil, boxes(told)), "sent again after that: not delivered twice"),
      allows(at(List(told), Map.empty).failing(true), Failed(Failure.StoreUnavailable), at(List(told), Map.empty),
        "the outbox cannot be read: nothing changes"),
      forbids(at(List(told), Map.empty).failing(false, true, true, true), (), at(Nil, Map.empty, now + 3),
        "a notice never leaves the outbox undelivered"))

  /** One person's notice: sent with retries; once the mail server has it, taken out of the outbox in one transaction.
    * Its failures end here: one notice failing never cancels another's delivery.
    */
  def deliverOne(n: Term[Notice]): Flow[Unit] =
    mailer.send(n).retry[Failure](retrying).attempt[Failure].flatMap(sent => Flow.whenA(sent.isRight)(
      Flow.atomically(store.load.flatMap(l => store.save(l.copy((outbox = l.outbox.filterNot(m => m === n)))))).attempt[Failure]))

  /** One run: the outbox read, and the oldest notice of each person in it delivered, four at once. DeliveryJob is proven
    * of it, on the store's, the mail server's and the clock's models, with its branches proven to commute.
    */
  def delivery: Flow[Unit] =
    for
      lib <- store.load
      _   <- firstOfEach(lib.outbox).parTraverseN(atOnce)(n => deliverOne(n))
    yield ()

  /** Delivery every ten seconds, run in the server. */
  val schedule: Every = Flow.every(10)(delivery)
