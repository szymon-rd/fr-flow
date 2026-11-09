package sharing.time

import frflow.*
import sharing.domain.*
import sharing.notifications.Notifications.mailOneAtATime
import sharing.notifications.Pool.poolOneAtATime
import sharing.store.LibraryStore.{libraryKept, libraryModel, libraryStarts, oneTransactionAtATime}
import sharing.time.ClockKept.*
import sharing.time.Lifetimes.*
import sharing.time.Run.*

/** The service's deadlines: what holds at every moment the service reaches, the World as it stands (owner §45 D,
  * §47), proven from what always holds of it as time passes; and those rules, each kept by every program changing
  * what it reads and by the world's own step, time passing. A change to a lifetime affects only the claims here.
  */
object Deadlines:
  val trashPurgedOnTime = Node.claim("While housekeeping runs at least every two minutes, no document stays in the " +
      "trash longer than 30 days and two minutes.")(
    libraryModel.current.documents.forall(doc =>
      doc.trashed.forall(at => clockModel.current < at + trashKeeps + housekeepingWithin)))
    .refines(sharing.trashUntilGone)

  val invitationsLapseOnTime = Node.claim("While housekeeping runs at least every two minutes, no invitation stays " +
      "pending longer than 7 days and two minutes after it was sent.")(
    libraryModel.current.invitations.forall(i => clockModel.current < i.sent + invitationLasts + housekeepingWithin))
    .refines(sharing.invitationsAreOffers)

  val requestsAnsweredOnTime = Node.claim("While housekeeping runs at least every two minutes, no access request " +
      "stays pending longer than 7 days and two minutes after it was made.")(
    libraryModel.current.requests.forall(r => clockModel.current < r.asked + requestLasts + housekeepingWithin))
    .refines(sharing.accessRequestsAreAsks)

  val remindersOnTime = Node.claim("While housekeeping runs at least every two minutes, no access request goes more " +
      "than 48 hours and two minutes without its reminder.")(
    libraryModel.current.requests.forall(r => r.reminded || clockModel.current < r.asked + remindAfter +
      housekeepingWithin))
    .refines(sharing.accessRequestsAreAsks)

  /** A root of its own: what makes clearing away the ended harmless, which no branch's step needs. */
  val endedStaysEnded = Node.claim("What has ended stays ended as time moves on.")(
    forall((s: Term[Share], i: Term[Invitation], doc: Term[Document], t: Term[BigInt], u: Term[BigInt]) =>
      ((t <= u && !inForce(s, t)) implies !inForce(s, u)) &&
      ((t <= u && !isOpen(i, t)) implies !isOpen(i, u)) &&
      ((t <= u && gone(doc, t)) implies gone(doc, u))))

  val endedSharesStayEnded = Node.claim("A share once ended stays ended at every later moment.")(
    forall((s: Term[Share], t: Term[BigInt], u: Term[BigInt]) => (t <= u && !inForce(s, t)) implies !inForce(s, u)))
    .refines(endedStaysEnded)

  val lapsedInvitationsStayLapsed = Node.claim("An invitation once lapsed stays lapsed at every later moment.")(
    forall((i: Term[Invitation], t: Term[BigInt], u: Term[BigInt]) => (t <= u && !isOpen(i, t)) implies !isOpen(i, u)))
    .refines(endedStaysEnded)

  val goneDocumentsStayGone = Node.claim("A document once gone stays gone at every later moment.")(
    forall((doc: Term[Document], t: Term[BigInt], u: Term[BigInt]) => (t <= u && gone(doc, t)) implies gone(doc, u)))
    .refines(endedStaysEnded)

  /** Today's clockNeverGoesBack, built into the clock now (owner §47) and a root of its own: no run and no step of the
    * world takes the time back, which each program and time passing are proven to keep (`isConstant`).
    */
  val timeMovesOn = Node.claim("A moment the service's time has reached is never left behind.")(
    forall((t: Term[BigInt]) => (t <= clockModel.current) implies (t <= clockModel.current).isConstant))
    .assuming(oneTransactionAtATime, mailOneAtATime, poolOneAtATime, housekeepingOnTime, housekeptOneAtATime)

  /** Housekeeping keeps up with the time: a rule of the clock and when housekeeping last ran, kept by time passing
    * where the schedule lets it pass (`housekeepingOnTime`).
    */
  val housekeptLately = Node.claim("Housekeeping last ran at a time already come, at most two minutes ago.")(
    always(clockModel, housekeptModel)((now, ran) => ran <= now && now <= ran + 120))
    .refines(trashPurgedOnTime, invitationsLapseOnTime, requestsAnsweredOnTime, remindersOnTime)
    .assuming(clockStarts, housekeptStarts, housekeptKept, housekeptOneAtATime, housekeepingOnTime)

  // What housekeeping leaves: rules of the library and of when housekeeping last ran, one a deadline.

  val trashNotGoneAtHousekeeping = Node.claim("No document in the trash was gone when housekeeping last ran.")(
    always(libraryModel, housekeptModel)((lib, ran) =>
      lib.documents.forall(doc => doc.trashed.forall(at => ran < at + 30 * 86400))))
    .refines(trashPurgedOnTime)
    .assuming(libraryKept, oneTransactionAtATime, libraryStarts, housekeptStarts, housekeptKept, housekeptOneAtATime)

  val invitationsOpenAtHousekeeping = Node.claim("No invitation had lapsed when housekeeping last ran.")(
    always(libraryModel, housekeptModel)((lib, ran) => lib.invitations.forall(i => ran < i.sent + 7 * 86400)))
    .refines(invitationsLapseOnTime)
    .assuming(libraryKept, oneTransactionAtATime, libraryStarts, housekeptStarts, housekeptKept, housekeptOneAtATime)

  val requestsPendingAtHousekeeping = Node.claim("No access request had lapsed when housekeeping last ran.")(
    always(libraryModel, housekeptModel)((lib, ran) => lib.requests.forall(r => ran < r.asked + 7 * 86400)))
    .refines(requestsAnsweredOnTime)
    .assuming(libraryKept, oneTransactionAtATime, libraryStarts, housekeptStarts, housekeptKept, housekeptOneAtATime)

  val remindedAtHousekeeping = Node.claim("No access request was due a reminder it had not had when housekeeping " +
      "last ran.")(
    always(libraryModel, housekeptModel)((lib, ran) =>
      lib.requests.forall(r => r.reminded || ran < r.asked + 2 * 86400)))
    .refines(remindersOnTime)
    .assuming(libraryKept, oneTransactionAtATime, libraryStarts, housekeptStarts, housekeptKept, housekeptOneAtATime)
