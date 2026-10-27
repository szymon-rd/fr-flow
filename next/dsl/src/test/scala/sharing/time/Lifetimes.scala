package sharing.time

import examples.Folds.*
import frflow.*
import sharing.domain.*

/** How long things last: when a share stops being in force, an invitation stops being open, and a document in the trash
  * is gone. Above this point the service speaks of these words only, and is proven for whatever they mean; here they
  * are fixed with the clock.
  */
object Lifetimes:
  val inForce = Definition[(Share, BigInt) => Boolean]("whether a share is in force at a moment: it gives access then")
  val isOpen = Definition[(Invitation, BigInt) => Boolean](
    "whether an invitation is open at a moment: it can be accepted then")
  val gone = Definition[(Document, BigInt) => Boolean](
    "whether a document is gone at a moment: past restoring, purged by the next housekeeping")
  val isPending = Definition[(AccessRequest, BigInt) => Boolean](
    "whether an access request is pending at a moment: it can be approved then")
  val reminderDue = Definition[(AccessRequest, BigInt) => Boolean](
    "whether the owner is due a reminder of an access request at a moment")

  // ---------------------------------------------------------------------------
  // the durations
  // ---------------------------------------------------------------------------

  val invitationLasts = Definition[BigInt]("how long an invitation stays open after it is sent, in seconds")
  val trashKeeps = Definition[BigInt]("how long a document stays in the trash before it is gone, in seconds")
  val requestLasts = Definition[BigInt]("how long an access request stays pending after it is made, in seconds")
  val remindAfter = Definition[BigInt](
    "how long after an access request is made its document's owner is reminded of it, in seconds")

  val requestLifetime = Node.claim("An access request stays pending for 7 days after it is made; its document's " +
      "owner is reminded of it after 48 hours.")(
    requestLasts === 7 * 86400 && remindAfter === 2 * 86400)

  val invitationLifetime = Node.claim("An invitation stays open for 7 days after it is sent.")(
    invitationLasts === 7 * 86400)

  val trashLifetime = Node.claim("A document stays in the trash for 30 days.")(trashKeeps === 30 * 86400)

  // ---------------------------------------------------------------------------
  // in force, open, gone
  // ---------------------------------------------------------------------------

  val inForceContract = Node.claim("A share is in force while now is before its end; a share with no end is always " +
      "in force.")(
    forall((s: Term[Share], t: Term[BigInt]) => inForce(s, t) === s.until.noneOr(end => t < end)))
    .leftOpenAbove
    .refines(Deadlines.endedStaysEnded)

  val inForceCode = define { (s: Term[Share], t: Term[BigInt]) => s.until.noneOr(end => t < end) }

  val isOpenContract = Node.claim("An invitation is open from its sending until 7 days after; then it has lapsed.")(
    forall((i: Term[Invitation], t: Term[BigInt]) => isOpen(i, t) === (t < i.sent + invitationLasts)))
    .leftOpenAbove
    .refines(sharing.invitations.Invitations.invitationsAreOffers, Deadlines.invitationsLapseOnTime,
      Deadlines.endedStaysEnded)

  val isOpenCode = define { (i: Term[Invitation], t: Term[BigInt]) => t < i.sent + invitationLasts }

  val goneContract = Node.claim("A document in the trash is gone 30 days after it was put there; a document not in " +
      "the trash is never gone.")(
    forall((doc: Term[Document], t: Term[BigInt]) => gone(doc, t) === doc.trashed.someWith(at => at + trashKeeps <= t)))
    .leftOpenAbove
    .refines(sharing.trash.Trash.trashUntilGone, Deadlines.trashPurgedOnTime, Deadlines.endedStaysEnded)

  val goneCode = define { (doc: Term[Document], t: Term[BigInt]) => doc.trashed.someWith(at => at + trashKeeps <= t) }

  val pendingContract = Node.claim("An access request is pending from when it is made until 7 days after; then it " +
      "has lapsed.")(
    forall((r: Term[AccessRequest], t: Term[BigInt]) => isPending(r, t) === (t < r.asked + requestLasts)))
    .leftOpenAbove
    .refines(sharing.requests.AccessRequests.accessRequestsAreAsks, Deadlines.requestsAnsweredOnTime)

  val isPendingCode = define { (r: Term[AccessRequest], t: Term[BigInt]) => t < r.asked + requestLasts }

  val reminderDueContract = Node.claim("The owner is due a reminder of an access request from 48 hours after it is " +
      "made.")(
    forall((r: Term[AccessRequest], t: Term[BigInt]) => reminderDue(r, t) === (r.asked + remindAfter <= t)))
    .leftOpenAbove
    .refines(sharing.requests.AccessRequests.accessRequestsAreAsks, Deadlines.requestsAnsweredOnTime)

  val reminderDueCode = define { (r: Term[AccessRequest], t: Term[BigInt]) => r.asked + remindAfter <= t }
