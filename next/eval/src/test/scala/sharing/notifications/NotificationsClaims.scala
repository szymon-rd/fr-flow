package sharing.notifications

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.notifications.Mailer.{mailbox, taken}
import sharing.notifications.Notifications.*
import sharing.store.LibraryStore.{libraryKept, libraryModel, oneTransactionAtATime}
import sharing.time.ClockKept.{clockAlone, clockKept}

/** Notifications's claims: what its code is proven to do, each refining a branch or the purpose. */
object NotificationsClaims:
  val announceContract = Node.claim("Announcing a change adds, at the end of the outbox, a notice of its entry to " +
      "each person it tells, as the library before the change says who: the person invited; whoever sent an " +
      "invitation now accepted; the owner of a document asked for; the person whose request was approved or " +
      "declined; the new owner of a document. Nothing else changes.")(
    forall((lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
      announce(lib, before, r, e) === lib.updated(_.outbox, lib.outbox ++ noticesOf(before, r, e))))
    .refines(noticesFollowChanges, sharing.auditTrail, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)

  val warnContract = Node.claim("Housekeeping tells of the shares ending within a day: at a moment, it adds at the " +
      "end of the outbox a notice, to each person a share reaches, of each share whose end comes a day on, within " +
      "one housekeeping period. Nothing else changes.")(
    forall((lib: Term[Library], t: Term[BigInt]) =>
      warn(lib, t) === lib.updated(_.outbox, lib.outbox ++ endingNotices(lib, t))))
    .refines(noticesFollowChanges)

  val deliveryJob = Node.claim("A run of delivery reads the outbox and sends the oldest notice of each person in it " +
      "to the mail server, four at once, each tried three times, a second and then two seconds apart. A notice " +
      "leaves the outbox only once the mail server has it, and only such a notice: one the mail server did not take " +
      "stays, to be sent at the next run. The mailbox of each person sent to is as it was, or holds that notice too. " +
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
