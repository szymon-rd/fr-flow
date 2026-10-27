package sharing.requests

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.requests.AccessRequests.*
import sharing.time.Lifetimes.isPending

/** AccessRequests's claims: what its code is proven to do, each refining a branch or the purpose. */
object AccessRequestsClaims:
  val askContract = Node.claim("A person asks for access to a document or a folder at a level: the request, made " +
      "now, takes the place of any earlier request of theirs for it. Asking for a document or folder that does not " +
      "exist changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      ask(lib, t, p, w, level) === when(holds(lib, w))(lib.updated(_.requests,
        make[AccessRequest](p, w, level, t, False) :: requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(accessRequestsAreAsks)

  val approveContract = Node.claim("Someone who may edit a document or folder approves a person's pending request " +
      "for it: the person then has a share of it at the level asked, for good, in place of any share of it they had, " +
      "and the request goes. Otherwise, or when it is the person's own document (their share of it is the owner's), " +
      "nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      approve(lib, t, by, p, w) ===
        lib.requests.find(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
          when(mayEdit(lib, t, by, w) && !ownedBy(lib, w, make[Grantee.Person](p)))(granted(lib, r)).otherwise(lib))))
    .refines(accessRequestsAreAsks)

  val declineContract = Node.claim("Someone who may edit a document or folder declines a person's request for it: " +
      "the request goes. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      decline(lib, t, by, p, w) ===
        when(mayEdit(lib, t, by, w))(lib.updated(_.requests, requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(accessRequestsAreAsks)

  val chaseContract = Node.claim("Housekeeping chases the access requests at a moment: a request no longer pending " +
      "is declined (it goes, and the person is told); a pending one due a reminder, not reminded yet, is marked " +
      "reminded and the owner of each document it is for is told. Everything else stays as it was.")(
    forall((lib: Term[Library], t: Term[BigInt]) => chase(lib, t) === lib
      .updated(_.requests, lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)))
      .updated(_.outbox, lib.outbox ++ chaseNotices(lib, t))))
    .refines(accessRequestsAreAsks)
