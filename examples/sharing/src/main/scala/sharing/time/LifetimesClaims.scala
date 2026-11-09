package sharing.time

import frflow.*
import sharing.domain.*
import sharing.time.Lifetimes.*

/** Lifetimes's claims: what its code is proven to do, each refining a branch or the purpose. */
object LifetimesClaims:
  /** How long a request lasts: today's `requestLifetime`, its first word. */
  val requestLifetime = Node.claim("An access request stays pending for 7 days after it is made.")(
    requestLasts === 7 * 86400)

  /** When a request is due a reminder: today's `requestLifetime`, its second word. */
  val reminderTime = Node.claim("An access request's document's owner is reminded of it after 48 hours.")(
    remindAfter === 2 * 86400)

  val invitationLifetime = Node.claim("An invitation stays open for 7 days after it is sent.")(
    invitationLasts === 7 * 86400)

  val trashLifetime = Node.claim("A document stays in the trash for 30 days.")(trashKeeps === 30 * 86400)

  val inForceContract = Node.claim("A share is in force until its end, when it has one.")(
    forall((s: Term[Share], t: Term[BigInt]) => inForce(s, t) === s.until.forall(end => t < end)))
    .leftOpenAbove
    .refines(Deadlines.endedSharesStayEnded)

  val isOpenContract = Node.claim("An invitation is open until 7 days after it is sent.")(
    forall((i: Term[Invitation], t: Term[BigInt]) => isOpen(i, t) === (t < i.sent + invitationLasts)))
    .leftOpenAbove
    .refines(sharing.invitationsAreOffers, Deadlines.lapsedInvitationsStayLapsed)

  val goneContract = Node.claim("A document is gone once 30 days have passed since it was put in the trash.")(
    forall((doc: Term[Document], t: Term[BigInt]) => gone(doc, t) === doc.trashed.exists(at => at + trashKeeps <= t)))
    .leftOpenAbove
    .refines(sharing.trashUntilGone, Deadlines.goneDocumentsStayGone)

  val pendingContract = Node.claim("An access request is pending until 7 days after it is made.")(
    forall((r: Term[AccessRequest], t: Term[BigInt]) => isPending(r, t) === (t < r.asked + requestLasts)))
    .leftOpenAbove
    .refines(sharing.accessRequestsAreAsks)

  val reminderDueContract = Node.claim("The owner is due a reminder of an access request from 48 hours after it is " +
      "made.")(
    forall((r: Term[AccessRequest], t: Term[BigInt]) => reminderDue(r, t) === (r.asked + remindAfter <= t)))
    .leftOpenAbove
    .refines(sharing.accessRequestsAreAsks)
