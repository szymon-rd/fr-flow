package sharing.time

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.invitations.Invitations
import sharing.requests.AccessRequests
import sharing.trash.Trash
import sharing.time.Lifetimes.*
import sharing.time.Run.*

// ============================================================================
// What the lifetimes mean for the service, with the clock. The purpose holds whatever the lifetimes are; a change to
// a lifetime affects only the claims here.
// ============================================================================

/** The service's deadlines: what holds at every moment, and of every run that keeps to its assumptions. */
object Deadlines:

  val trashPurgedOnTime = Node.claim("TrashPurgedOnTime",
    "While housekeeping runs at least every two minutes, no document stays in the trash longer than 30 days and two minutes.",
    why = "Q8 as a bounded response: every moment the service reaches, given the scheduler's period (HousekeepingOnTime). Unbounded \"eventually purged\" is weaker and could not be tested. That housekeeping never purges before is HousekeepingClearsOnlyTheEnded's, with GoneContract.",
    idea = "Trash"
  )(after(events).library.documents.forall(doc => doc.trashed.fold(True)(at => after(events).now < at + trashKeeps + housekeepingWithin)))
    .under(Trash.trashUntilGone)

  val invitationsLapseOnTime = Node.claim("InvitationsLapseOnTime",
    "While housekeeping runs at least every two minutes, no invitation stays pending longer than 7 days and two minutes after it was sent.",
    why = "Q7: an invitation lapses after 7 days, and housekeeping removes it at its next run (HousekeepingOnTime).",
    idea = "Invitations"
  )(after(events).library.invitations.forall(i => after(events).now < i.sent + invitationLasts + housekeepingWithin))
    .under(Invitations.invitationsAreOffers)

  val requestsAnsweredOnTime = Node.claim("RequestsAnsweredOnTime",
    "While housekeeping runs at least every two minutes, no access request stays pending longer than 7 days and two minutes after it was made, and none goes more than 48 hours and two minutes without its reminder.",
    why = "Q12: a reminder after 48 h and a decline after 7 days, as bounded responses, given the scheduler's period (HousekeepingOnTime).",
    idea = "Access requests"
  )(after(events).library.requests.forall(r => after(events).now < r.asked + requestLasts + housekeepingWithin &&
    (r.reminded || after(events).now < r.asked + remindAfter + housekeepingWithin)))
    .under(AccessRequests.requestsAreAsks)

  val endedStaysEnded = Node.claim("EndedStaysEnded",
    "What has ended stays ended: time in the service never goes back, so a share once ended, an invitation once lapsed and a document once gone stay so for the rest of the run.",
    why = "Stability in time: these facts change only one way, which is what lets the service cache them and housekeeping remove them for good. It rests on the clock never going back (ClockNeverGoesBack).",
    idea = "Time and housekeeping"
  )(forall((pre: Term[List[Event]], post: Term[List[Event]]) => (events === pre ++ post) ==> (after(pre).now <= after(events).now)) &&
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) ==>
      (forall((s: Term[Share]) => !inForce(s, t) ==> !inForce(s, u)) &&
       forall((i: Term[Invitation]) => !isOpen(i, t) ==> !isOpen(i, u)) &&
       forall((doc: Term[Document]) => gone(doc, t) ==> gone(doc, u)))))
    .under(Housekeeping.clearsOnlyTheEnded)
