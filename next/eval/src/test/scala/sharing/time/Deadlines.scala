package sharing.time

import frflow.*
import sharing.domain.*
import sharing.time.Lifetimes.*
import sharing.time.Run.*

/** The service's deadlines: what holds at every moment, and of every run that keeps to its assumptions. What the
  * lifetimes mean for the service, with the clock; a change to a lifetime affects only the claims here.
  */
object Deadlines:
  val trashPurgedOnTime = Node.claim("While housekeeping runs at least every two minutes, no document stays in the " +
      "trash longer than 30 days and two minutes.")(
    after(events).library.documents.forall(doc =>
      doc.trashed.forall(at => after(events).now < at + trashKeeps + housekeepingWithin)))
    .refines(sharing.trashUntilGone)
    .assuming(clockNeverGoesBack, housekeepingOnTime)

  val invitationsLapseOnTime = Node.claim("While housekeeping runs at least every two minutes, no invitation stays " +
      "pending longer than 7 days and two minutes after it was sent.")(
    after(events).library.invitations.forall(i => after(events).now < i.sent + invitationLasts + housekeepingWithin))
    .refines(sharing.invitationsAreOffers)
    .assuming(clockNeverGoesBack, housekeepingOnTime)

  val requestsAnsweredOnTime = Node.claim("While housekeeping runs at least every two minutes, no access request " +
      "stays pending longer than 7 days and two minutes after it was made, and none goes more than 48 hours and two " +
      "minutes without its reminder.")(
    after(events).library.requests.forall(r => after(events).now < r.asked + requestLasts + housekeepingWithin &&
      (r.reminded || after(events).now < r.asked + remindAfter + housekeepingWithin)))
    .refines(sharing.accessRequestsAreAsks)
    .assuming(clockNeverGoesBack, housekeepingOnTime)

  val endedStaysEnded = Node.claim("What has ended stays ended: time in the service never goes back, so a share once " +
      "ended, an invitation once lapsed and a document once gone stay so for the rest of the run.")(
    forall((pre: Term[List[Event]], post: Term[List[Event]]) =>
      (events === pre ++ post) implies (after(pre).now <= after(events).now)) &&
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) implies
      (forall((s: Term[Share]) => !inForce(s, t) implies !inForce(s, u)) &&
        forall((i: Term[Invitation]) => !isOpen(i, t) implies !isOpen(i, u)) &&
        forall((doc: Term[Document]) => gone(doc, t) implies gone(doc, u)))))
    .refines(sharing.housekeepingClearsOnlyTheEnded)
    .assuming(clockNeverGoesBack)
