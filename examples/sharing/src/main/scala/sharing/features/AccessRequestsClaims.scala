package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.AccessRequests.*
import sharing.time.Lifetimes.isPending

/** AccessRequests's claims: what its code is proven to do, each refining a branch or the purpose. */
object AccessRequestsClaims:
  val askContract = Node.claim("Asking for a document or folder that exists puts a request made now in place of any " +
      "earlier request of the person's for it, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      ask(lib, t, p, w, level) === when(holds(lib, w))(lib.updated(_.requests,
        make[AccessRequest](p, w, level, t, False) :: requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(askingChangesNothingKept)

  val approveContract = Node.claim("Approving a pending request, asked by someone who may edit and not of the " +
      "person's own document, turns it into a share for good at the level asked, in place of any share they had, and " +
      "otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      approve(lib, t, by, p, w) ===
        lib.requests.find(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
          when(mayEdit(lib, t, by, w) && !ownedBy(lib, w, make[Grantee.Person](p)))(granted(lib, r)).otherwise(lib))))
    .refines(onlyEditorsAnswer, approvedOnlyWhilePending)

  val declineContract = Node.claim("Declining, asked by someone who may edit, removes the person's request for the " +
      "document or folder, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      decline(lib, t, by, p, w) ===
        when(mayEdit(lib, t, by, w))(lib.updated(_.requests, requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(onlyEditorsAnswer)

  val chaseContract = Node.claim("Chasing the access requests at a moment drops each one no longer pending and marks " +
      "reminded each one newly due a reminder, putting a notice of each in the outbox.")(
    forall((lib: Term[Library], t: Term[BigInt]) => chase(lib, t) === lib
      .updated(_.requests, lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)))
      .updated(_.outbox, lib.outbox ++ chaseNotices(lib, t))))
    .refines(accessRequestsAreAsks)
