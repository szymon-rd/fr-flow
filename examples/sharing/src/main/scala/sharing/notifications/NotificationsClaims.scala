package sharing.notifications

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.notifications.Notifications.*
import sharing.store.LibraryStore.{libraryModel, oneTransactionAtATime}
import sharing.time.ClockKept.housekeepingOnTime

/** Notifications's claims: what its code is proven to do, each refining a branch or the purpose. */
object NotificationsClaims:
  val announceContract = Node.claim("Announcing a change adds at the end of the outbox a notice of its entry to each " +
      "person the change concerns, as the library before it says, and changes nothing else.")(
    forall((lib: Term[Library], before: Term[Library], r: Term[Request], e: Term[Entry]) =>
      announce(lib, before, r, e) === lib.updated(_.outbox, lib.outbox ++ noticesOf(before, r, e))))
    .refines(noticesFollowChanges, sharing.auditTrail)

  val warnContract = Node.claim("Housekeeping adds at the end of the outbox a notice, to each person a share " +
      "reaches, of each share whose end comes a day on, within one housekeeping period, and changes nothing else.")(
    forall((lib: Term[Library], t: Term[BigInt]) =>
      warn(lib, t) === lib.updated(_.outbox, lib.outbox ++ endingNotices(lib, t))))
    .refines(noticesFollowChanges)

  val deliveryJob = Node.claim("A run of delivery sends the oldest notice of each person in the outbox to the mail " +
      "server, and takes out of the outbox only what the mail server took.") {
    val after = deliver.after
    deliver.result.fold(
      _ => libraryModel.in(after) === libraryModel.current && mailerModel.in(after) === mailerModel.current,
      _ =>
        onlyTakenOut(libraryModel.current, libraryModel.in(after)) &&
          libraryModel.current.outbox.forall(n => libraryModel.in(after).outbox.contains(n) ||
            sentFrom(libraryModel.current.outbox, mailerModel.in(after), n)) &&
          firstOfEach(libraryModel.current.outbox).forall(n =>
            tookAtMost(mailerModel.current, mailerModel.in(after), n)))
  }
    .refines(noticesFollowChanges)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)

  val failedDeliveryChangesNothing = Node.claim("A run of delivery that cannot read the outbox changes nothing.")(
    deliver.result.fold(_ => libraryModel.in(deliver.after) === libraryModel.current &&
      mailerModel.in(deliver.after) === mailerModel.current, _ => True))
    .refines(deliveryJob)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)

  val deliveryOnlyEmptiesTheOutbox = Node.claim("A run of delivery changes nothing in the library but taking notices " +
      "out of the outbox.")(
    deliver.result.fold(_ => True, _ => onlyTakenOut(libraryModel.current, libraryModel.in(deliver.after))))
    .refines(deliveryJob)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)

  val deliveryTakesOutOnlyWhatWasSent = Node.claim("A notice leaves the outbox only once it was sent as the oldest " +
      "of its person's and the mail server has it.")(
    deliver.result.fold(_ => True, _ => libraryModel.current.outbox.forall(n =>
      libraryModel.in(deliver.after).outbox.contains(n) ||
        sentFrom(libraryModel.current.outbox, mailerModel.in(deliver.after), n))))
    .refines(deliveryJob)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)

  val deliveryTouchesOnlyWhatItSends = Node.claim("The mailbox of each person sent to is as it was, or holds the " +
      "notice sent too.")(
    deliver.result.fold(_ => True, _ => firstOfEach(libraryModel.current.outbox).forall(n =>
      tookAtMost(mailerModel.current, mailerModel.in(deliver.after), n))))
    .refines(deliveryJob)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)

  /** A root of its own (owner §11): what the kept combinators' bracket is for, which no branch about notices makes. */
  val deliveryGivesBack = Node.claim("A run of delivery leaves as many connections to the mail server in use as " +
      "before, however it ends.")(
    Pool.poolModel.in(deliver.after) === Pool.poolModel.current)
    .assuming(oneTransactionAtATime, mailOneAtATime, Pool.poolOneAtATime, housekeepingOnTime)
