package sharing.notifications

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.requests.AccessRequests
import sharing.store.LibraryStore.store
import sharing.time.ClockKept.clock

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

  val mailer = Boundary.failing[Mailer, Failure]("the mail server the service sends notices to; it may be down",
    Failure.MailerUnavailable)
  val mailerModel = mailer.model("each person's mailbox at the mail server")(Mailboxes(_))

  val mailerKept = Node.assumption("The mail server delivers a notice it is given into the mailbox of the person it " +
      "is to, after the ones delivered there before, and one it has already delivered is not delivered again; any " +
      "call may fail because it is down, and then delivers nothing.")(
    mailer.behavesAs(mailerModel))

  val mailOneAtATime = Node.assumption("The mail server takes one notice at a time: two deliveries never interleave.")(
    mailer.atomic)

  /** The notices a change made by a request tells of, logged as `e`, on the library `lib` it was made on: the person
    * invited; the person who sent an invitation now accepted; the owner of a document asked for; the person whose
    * request was approved or declined; the new owner. Other changes tell nobody.
    */
  private val noNotices: Term[List[Notice]] = Nil
  val noticesOf = define { (lib: Term[Library], r: Term[Request], e: Term[Entry]) =>
    val nobody: Term[List[Notice]] = Nil
    val logged = make[Subject.Logged](e)
    r.on[Request.Access]((_, _) => nobody)
      .on[Request.Share]((_, _, _, _, _) => nobody)
      .on[Request.Unshare]((_, _, _) => nobody)
      .on[Request.Move]((_, _, _) => nobody)
      .on[Request.Invite]((_, to, _, _) => make[Notice](to, logged) :: noNotices)
      .on[Request.Accept]((p, what) =>
        lib.invitations.filter(i => i.to === p && i.what === what).map(i => make[Notice](i.by, logged)))
      .on[Request.Withdraw]((_, _, _) => nobody)
      .on[Request.Trash]((_, _) => nobody)
      .on[Request.Restore]((_, _) => nobody)
      .on[Request.Ask]((_, w, _) =>
        lib.documents.filter(doc => AccessRequests.isFor(w, doc)).map(doc => make[Notice](doc.owner, logged)))
      .on[Request.Approve]((_, p, _) => make[Notice](p, logged) :: noNotices)
      .on[Request.Decline]((_, p, _) => make[Notice](p, logged) :: noNotices)
      .on[Request.Transfer]((_, _, to) => make[Notice](to, logged) :: noNotices) }

  val announceCode = define { (lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
    lib.updated(_.outbox, lib.outbox ++ noticesOf(before, r, e)) }

  // ---------------------------------------------------------------------------
  // shares ending within a day: housekeeping tells the people they reach
  // ---------------------------------------------------------------------------

  /** The people a share reaches, by name: the person it is with, or the members of the team. */
  val reachedBy = define { (lib: Term[Library], s: Term[Share]) =>
    s.withWhom.on[Grantee.Person](p => p :: (Nil: Term[List[PersonId]]))
      .on[Grantee.Team](t => lib.teams.filter(team => team.id === t).flatMap(team => team.members)) }
  /** The window a share's end is told of in: two minutes, the longest housekeeping goes without a run. */
  val window: BigInt = 120
  val day: BigInt = 86400
  /** Whether a share ends a day after a moment, within the window. */
  val endsInADay = define { (s: Term[Share], t: Term[BigInt]) =>
    s.until.exists(u => u <= t + day && u > t + day - window) }
  /** The notices of the shares ending in a day, to each person each reaches. */
  val endingNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.filter(s => endsInADay(s, t))
      .flatMap(s => reachedBy(lib, s).map(p => make[Notice](p, make[Subject.Ending](s)))) }

  val warnCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.outbox, lib.outbox ++ endingNotices(lib, t)) }

  // ---------------------------------------------------------------------------
  // delivery: the outbox sent to the mail server, every person's oldest notice, four at once, retried
  // ---------------------------------------------------------------------------

  /** The oldest notice of each person in an outbox, in the outbox's order: what a run of delivery sends. */
  val firstOfEach = define { (outbox: Term[List[Notice]]) =>
    outbox.filter(n => outbox.find(m => m.to === n.to) === some(n)) }

  val delivery = program { Delivery(store.recording, mailer.recording, clock.recording).run }
