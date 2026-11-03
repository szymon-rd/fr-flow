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
      "stays pending longer than 7 days and two minutes after it was made, and none goes more than 48 hours and two " +
      "minutes without its reminder.")(
    libraryModel.current.requests.forall(r => clockModel.current < r.asked + requestLasts + housekeepingWithin &&
      (r.reminded || clockModel.current < r.asked + remindAfter + housekeepingWithin)))
    .refines(sharing.accessRequestsAreAsks)

  val endedStaysEnded = Node.claim("What has ended stays ended as time moves on: a share once ended, an invitation " +
      "once lapsed and a document once gone stay so at every later moment.")(
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) implies
      (forall((s: Term[Share]) => !inForce(s, t) implies !inForce(s, u)) &&
        forall((i: Term[Invitation]) => !isOpen(i, t) implies !isOpen(i, u)) &&
        forall((doc: Term[Document]) => gone(doc, t) implies gone(doc, u)))))
    .refines(sharing.housekeepingClearsOnlyTheEnded)

  /** Today's clockNeverGoesBack, built into the clock now (owner §47) and a root of its own: no run and no step of the
    * world takes the time back, which each program and time passing are proven to keep (`isConstant`).
    */
  val timeMovesOn = Node.claim("Time in the service never goes back: a moment once reached is never left behind.")(
    forall((t: Term[BigInt]) => (t <= clockModel.current) implies (t <= clockModel.current).isConstant))
    .assuming(oneTransactionAtATime, mailOneAtATime, poolOneAtATime, housekeepingOnTime)

  /** Housekeeping keeps up with the time: a rule of the clock and when housekeeping last ran, kept by time passing
    * where the schedule lets it pass (`housekeepingOnTime`).
    */
  val housekeptLately = Node.claim("Housekeeping last ran at a time already come, at most two minutes ago.")(
    always(clockModel, housekeptModel)((now, ran) => ran <= now && now <= ran + 120))
    .refines(trashPurgedOnTime, invitationsLapseOnTime, requestsAnsweredOnTime)
    .assuming(clockStarts, housekeptStarts, housekeptKept, housekeptOneAtATime, housekeepingOnTime)

  /** What housekeeping leaves: a rule of the library and when housekeeping last ran. */
  val nothingEndedAtHousekeeping = Node.claim("Nothing the library holds had ended when housekeeping last ran: no " +
      "document in the trash was gone, no invitation had lapsed, no access request had lapsed, and none was due a " +
      "reminder it had not had.")(
    always(libraryModel, housekeptModel)((lib, ran) =>
      lib.documents.forall(doc => doc.trashed.forall(at => ran < at + 30 * 86400)) &&
        lib.invitations.forall(i => ran < i.sent + 7 * 86400) &&
        lib.requests.forall(r => ran < r.asked + 7 * 86400 && (r.reminded || ran < r.asked + 2 * 86400))))
    .refines(trashPurgedOnTime, invitationsLapseOnTime, requestsAnsweredOnTime)
    .assuming(libraryKept, oneTransactionAtATime, libraryStarts, housekeptStarts, housekeptKept, housekeptOneAtATime)
