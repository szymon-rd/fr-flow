package sharing.notifications

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.notifications.Mailer.{mailbox, taken}
import sharing.requests.AccessRequests
import sharing.store.LibraryStore.{libraryKept, libraryModel, oneTransactionAtATime, store}
import sharing.time.ClockKept.{clock, clockAlone, clockKept}
import sharing.time.Run.{after, events}

/** Notifications: a change that concerns someone puts a notice of it in the outbox, in the same save as the change;
  * delivery sends the outbox to the mail server, a notice leaving the outbox only once the mail server has it. The
  * mail server keeps each person's notices in the order it got them, and takes a notice once.
  */
object Notifications:
  val announce = Definition[(Library, Library, Request, Entry) => Library](
    "the library with notices of a change added to its outbox")
  val warn = Definition[(Library, BigInt) => Library]("the library with notices of the shares ending within a day")
  val deliver = Definition[Program[Unit]](
    "a run of delivery: the oldest notice of each person in the outbox sent to the mail server")

  val mailer = Boundary.failing[Mailer, Failure]("the mail server the service sends notices to; it may be down")
  val mailerModel = mailer.model("each person's mailbox at the mail server")(Mailboxes(_))

  val mailerKept = Node.assumption("The mail server delivers a notice it is given into the mailbox of the person it " +
      "is to, after the ones delivered there before, and one it has already delivered is not delivered again; any " +
      "call may fail because it is down, and then delivers nothing.")(
    mailer.behavesAs(mailerModel))

  val mailOneAtATime = Node.assumption("The mail server takes one notice at a time: two deliveries never interleave.")(
    mailerModel.changedOneRunAtATime)

  /** The notices a change made by a request tells of, logged as `e`, on the library `lib` it was made on: the person
    * invited; the person who sent an invitation now accepted; the owner of a document asked for; the person whose
    * request was approved or declined; the new owner. Other changes tell nobody.
    */
  val noticesOf = define { (lib: Term[Library], r: Term[Request], e: Term[Entry]) =>
    val nobody: Term[List[Notice]] = Nil
    val logged = make[Subject.Logged](e)
    r.on[Request.Access]((_, _) => nobody)
      .on[Request.Share]((_, _, _, _, _) => nobody)
      .on[Request.Unshare]((_, _, _) => nobody)
      .on[Request.Move]((_, _, _) => nobody)
      .on[Request.Invite]((_, to, _, _) => one(make[Notice](to, logged)))
      .on[Request.Accept]((p, what) =>
        lib.invitations.filter(i => i.to === p && i.what === what).mapped(i => make[Notice](i.by, logged)))
      .on[Request.Withdraw]((_, _, _) => nobody)
      .on[Request.Trash]((_, _) => nobody)
      .on[Request.Restore]((_, _) => nobody)
      .on[Request.Ask]((_, w, _) =>
        lib.documents.filter(doc => AccessRequests.isFor(w, doc)).mapped(doc => make[Notice](doc.owner, logged)))
      .on[Request.Approve]((_, p, _) => one(make[Notice](p, logged)))
      .on[Request.Decline]((_, p, _) => one(make[Notice](p, logged)))
      .on[Request.Transfer]((_, _, to) => one(make[Notice](to, logged))) }

  /** The branch: what a notice is. */
  val noticesFollowChanges = Node.claim("A notice is sent only of a change already kept: at every moment, every " +
      "notice of a logged change waiting in the outbox is of an entry in the log. A notice leaves the outbox only " +
      "once the mail server has it, and the mail server has each notice once, so a person is told of each event at " +
      "least once and never twice.")(
    after(events).library.outbox.forall(n => n.about
      .on[Subject.Logged](e => after(events).library.log.contains(e))
      .on[Subject.Reminder](_ => True)
      .on[Subject.Lapsed](_ => True)
      .on[Subject.Ending](_ => True)) &&
    after(events).mailbox.forall(n => after(events).mailbox.filter(m => m === n).length === 1))
    .refines(accessFollowsShares)

  val announceContract = Node.claim("Announcing a change adds, at the end of the outbox, a notice of its entry to " +
      "each person it tells, as the library before the change says who: the person invited; whoever sent an " +
      "invitation now accepted; the owner of a document asked for; the person whose request was approved or " +
      "declined; the new owner of a document. Nothing else changes.")(
    forall((lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
      announce(lib, before, r, e) === lib.updated(_.outbox, lib.outbox ++ noticesOf(before, r, e))))
    .refines(noticesFollowChanges, sharing.audit.Audit.auditTrail, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)

  val announceCode = define { (lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
    lib.updated(_.outbox, lib.outbox ++ noticesOf(before, r, e)) }

  // ---------------------------------------------------------------------------
  // shares ending within a day: housekeeping tells the people they reach
  // ---------------------------------------------------------------------------

  /** The people a share reaches, by name: the person it is with, or the members of the team. */
  val reachedBy = define { (lib: Term[Library], s: Term[Share]) =>
    s.withWhom.on[Grantee.Person](p => one(p))
      .on[Grantee.Team](t => lib.teams.filter(team => team.id === t).flatMapped(team => team.members)) }
  /** The window a share's end is told of in: two minutes, the longest housekeeping goes without a run. */
  val window: BigInt = 120
  val day: BigInt = 86400
  /** Whether a share ends a day after a moment, within the window. */
  val endsInADay = define { (s: Term[Share], t: Term[BigInt]) =>
    s.until.someWith(u => u <= t + day && u > t + day - window) }
  /** The notices of the shares ending in a day, to each person each reaches. */
  val endingNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.filter(s => endsInADay(s, t))
      .flatMapped(s => reachedBy(lib, s).mapped(p => make[Notice](p, make[Subject.Ending](s)))) }

  val warnContract = Node.claim("Housekeeping tells of the shares ending within a day: at a moment, it adds at the " +
      "end of the outbox a notice, to each person a share reaches, of each share whose end comes a day on, within " +
      "one housekeeping period. Nothing else changes.")(
    forall((lib: Term[Library], t: Term[BigInt]) =>
      warn(lib, t) === lib.updated(_.outbox, lib.outbox ++ endingNotices(lib, t))))
    .refines(noticesFollowChanges)

  val warnCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.outbox, lib.outbox ++ endingNotices(lib, t)) }

  // ---------------------------------------------------------------------------
  // delivery: the outbox sent to the mail server, every person's oldest notice at once, retried
  // ---------------------------------------------------------------------------

  /** The oldest notice of each person in an outbox, in the outbox's order: what a run of delivery sends. */
  val firstOfEach = define { (outbox: Term[List[Notice]]) =>
    outbox.filter(n => outbox.firstWhere(m => m.to === n.to) === some(n)) }

  val deliveryJob = Node.claim("A run of delivery reads the outbox and sends the oldest notice of each person in it " +
      "to the mail server, all at once, each tried three times, a second and then two seconds apart. A notice leaves " +
      "the outbox only once the mail server has it, and only such a notice: one the mail server did not take stays, " +
      "to be sent at the next run. The mailbox of each person sent to is as it was, or holds that notice too. " +
      "Nothing else in the library changes. When the outbox cannot be read, nothing changes.")(
    forall((before: Term[World]) => deliver.from(before) { (_, after) =>
      val (was, is) = (libraryModel.in(before), libraryModel.in(after))
      let(firstOfEach(was.outbox))(heads =>
        is === was.updated(_.outbox, was.outbox.filter(n => is.outbox.contains(n))) &&
          was.outbox.forall(n => is.outbox.contains(n) ||
            (heads.contains(n) && mailbox(mailerModel.in(after), n.to).contains(n))) &&
          heads.forall(n => mailbox(mailerModel.in(after), n.to) === mailbox(mailerModel.in(before), n.to) ||
            mailbox(mailerModel.in(after), n.to) === taken(mailbox(mailerModel.in(before), n.to), n))) }
      .failing { (_: Term[Failure], after) =>
        libraryModel.in(after) === libraryModel.in(before) && mailerModel.in(after) === mailerModel.in(before) }))
    .refines(noticesFollowChanges)
    .assuming(libraryKept, oneTransactionAtATime, mailerKept, mailOneAtATime, clockKept, clockAlone)

  val delivery = program { Delivery(store.recording, mailer.recording, clock.recording).run }
