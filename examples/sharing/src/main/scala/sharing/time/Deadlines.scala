package sharing.time

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.invitations.Invitations
import sharing.service.Sharing
import sharing.time.Lifetimes.*
import sharing.time.Run.*

// ============================================================================
// What the lifetimes mean for the service, with the clock: the claims below the timed words. The purpose above says
// none of this; it holds whatever the lifetimes are. A change to a lifetime brings back only what is stated here.
// ============================================================================

/** The service's deadlines: what holds at every moment, and of every run that keeps to its assumptions. */
object Deadlines:

  val expiredSharesGiveNoAccess = Node.claim("ExpiredSharesGiveNoAccess",
    "A share gives no access from its end on, whether or not housekeeping has removed it: a person's access is what the shares not yet ended give.",
    why = "Q6: access stops at the end time even before the job runs; the meaning reads the clock, the job only tidies. Stated of the service's code for access.",
    idea = "Expiring shares"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.accessCode(lib, t, p, d) ===
      Sharing.accessCode(lib.copy((shares = lib.shares.filter(s => s.until.fold(True)(end => t < end)))), t, p, d)))
    .under(accessFollowsShares)

  val invitationsAcceptedInTime = Node.claim("InvitationsAcceptedInTime",
    "An invitation is accepted only within 7 days of its sending.",
    why = "Q7: an invitation lapses after 7 days. Stated of the service's code for accepting.",
    idea = "Invitations"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    Invitations.acceptCode(lib, t, p, what) =!= lib ==>
      lib.invitations.exists(i => i.to === p && i.what === what && t < i.sent + invitationLasts)))
    .under(accessFollowsShares)

  val trashPurgedOnTime = Node.claim("TrashPurgedOnTime",
    "A document in the trash is purged after 30 days and never before: housekeeping removes only documents 30 days in the trash, and while it runs at least every two minutes no document stays in the trash longer than 30 days and two minutes.",
    why = "Q8, as a safety (never before: each run of housekeeping) and a bounded response (after: every moment the service reaches, given the scheduler's period, HousekeepingOnTime). Unbounded \"eventually purged\" is weaker and could not be tested.",
    idea = "Trash"
  )(forall((lib: Term[Library], t: Term[BigInt]) =>
    lib.documents.forall(doc => Housekeeping.tidyCode(lib, t).documents.contains(doc) || doc.trashed.fold(False)(at => at + trashKeeps <= t))) &&
    after(events).library.documents.forall(doc => doc.trashed.fold(True)(at => after(events).now < at + trashKeeps + housekeepingWithin)))
    .under(accessFollowsShares)

  val invitationsLapseOnTime = Node.claim("InvitationsLapseOnTime",
    "While housekeeping runs at least every two minutes, no invitation stays pending longer than 7 days and two minutes after it was sent.",
    why = "Q7: an invitation lapses after 7 days, and housekeeping removes it at its next run (HousekeepingOnTime).",
    idea = "Invitations"
  )(after(events).library.invitations.forall(i => after(events).now < i.sent + invitationLasts + housekeepingWithin))
    .under(accessFollowsShares)

  val endedStaysEnded = Node.claim("EndedStaysEnded",
    "What has ended stays ended: time in the service never goes back, so a share once ended, an invitation once lapsed and a document once gone stay so for the rest of the run.",
    why = "Stability in time: these facts change only one way, which is what lets the service cache them and housekeeping remove them for good. It rests on the clock never going back (ClockNeverGoesBack).",
    idea = "Time and housekeeping"
  )(forall((pre: Term[List[Event]], post: Term[List[Event]]) => (events === pre ++ post) ==> (after(pre).now <= after(events).now)) &&
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) ==>
      (forall((s: Term[Share]) => !inForce(s, t) ==> !inForce(s, u)) &&
       forall((i: Term[Invitation]) => !isOpen(i, t) ==> !isOpen(i, u)) &&
       forall((doc: Term[Document]) => gone(doc, t) ==> gone(doc, u)))))
    .under(accessFollowsShares)
