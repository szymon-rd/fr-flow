package sharing.invitations

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.invitations.Invitations.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen

/** Invitations's claims: what its code is proven to do, each refining a branch or the purpose. */
object InvitationsClaims:
  val inviteContract = Node.claim("Someone who may edit a document or folder invites a person to it at a level: the " +
      "invitation, sent now, takes the place of any earlier invitation of them to it. When anyone else asks, nothing " +
      "changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
        level: Term[Level]) => invite(lib, t, by, to, what, level) === when(mayEdit(lib, t, by, what))(
      lib.updated(_.invitations, make[Invitation](to, what, level, by, t) :: invitationsWithout(lib.invitations, to,
        what))).otherwise(lib)))
    .refines(invitationsAreOffers)

  val acceptContract = Node.claim("A person accepts their open invitation to a document or folder: they then have a " +
      "share of it at the invitation's level, in place of any share of it they had, and the invitation goes. Without " +
      "an open invitation, or when the document is their own (their share of it is the owner's), nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
      accept(lib, t, p, what) ===
        lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
          when(ownedBy(lib, what, make[Grantee.Person](p)))(lib).otherwise(lib
            .updated(_.shares, make[Share](what, make[Grantee.Person](p), i.level, none[BigInt]) ::
              sharesWithout(lib.shares, what, make[Grantee.Person](p)))
            .updated(_.invitations, invitationsWithout(lib.invitations, p, what))))))
    .refines(invitationsAreOffers)

  val withdrawContract = Node.claim("Someone who may edit a document or folder withdraws a person's invitation to " +
      "it: the invitation goes. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      withdraw(lib, t, by, to, what) === when(mayEdit(lib, t, by, what))(
        lib.updated(_.invitations, invitationsWithout(lib.invitations, to, what))).otherwise(lib)))
    .refines(invitationsAreOffers)
