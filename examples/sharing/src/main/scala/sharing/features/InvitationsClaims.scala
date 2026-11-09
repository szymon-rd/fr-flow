package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Invitations.*
import sharing.features.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen

/** Invitations's claims: what its code is proven to do, each refining a branch or the purpose. */
object InvitationsClaims:
  val inviteContract = Node.claim("Inviting, asked by someone who may edit, puts an invitation sent now in place of " +
      "any earlier invitation of the person to the same document or folder, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
        level: Term[Level]) => invite(lib, t, by, to, what, level) === when(mayEdit(lib, t, by, what))(
      lib.updated(_.invitations, make[Invitation](to, what, level, by, t) :: invitationsWithout(lib.invitations, to,
        what))).otherwise(lib)))
    .refines(onlyEditorsInvite, invitingGivesNoAccess)

  val acceptContract = Node.claim("Accepting an open invitation to anything but the person's own document turns it " +
      "into a share at its level, in place of any share they had, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
      accept(lib, t, p, what) ===
        lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
          when(ownedBy(lib, what, make[Grantee.Person](p)))(lib).otherwise(lib
            .updated(_.shares, make[Share](what, make[Grantee.Person](p), i.level, none[BigInt]) ::
              sharesWithout(lib.shares, what, make[Grantee.Person](p)))
            .updated(_.invitations, invitationsWithout(lib.invitations, p, what))))))
    .refines(onlyTheInvitedAccept)

  val withdrawContract = Node.claim("Withdrawing, asked by someone who may edit, removes the person's invitation to " +
      "the document or folder, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      withdraw(lib, t, by, to, what) === when(mayEdit(lib, t, by, what))(
        lib.updated(_.invitations, invitationsWithout(lib.invitations, to, what))).otherwise(lib)))
    .refines(onlyEditorsInvite)
