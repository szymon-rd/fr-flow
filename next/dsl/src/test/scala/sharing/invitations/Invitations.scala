package sharing.invitations

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen
import sharing.time.Run.{after, events, housekeepingWithin}

/** Invitations: someone who may edit a document or folder invites a person to it; the person accepts while the
  * invitation is open, and only then has the share. Each operation is a function of the library and of the moment.
  */
object Invitations:
  val invite = Definition[(Library, BigInt, PersonId, PersonId, Target, Level) => Library](
    "the library after someone asks to invite a person")
  val accept = Definition[(Library, BigInt, PersonId, Target) => Library](
    "the library after a person asks to accept an invitation")
  val withdraw = Definition[(Library, BigInt, PersonId, PersonId, Target) => Library](
    "the library after someone asks to withdraw an invitation")

  /** The branch: what an invitation is. */
  val invitationsAreOffers = Node.claim("An invitation is an offer from someone who may edit: only they send it or " +
      "take it back, it gives nobody access, it is taken up only by the person invited while it is open, and " +
      "housekeeping clears it away within one of its periods of its lapsing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      (withdraw(lib, t, by, to, what) =!= lib implies mayEdit(lib, t, by, what)) &&
        forall((level: Term[Level]) =>
          (invite(lib, t, by, to, what, level) =!= lib implies mayEdit(lib, t, by, what)) &&
          forall((p: Term[PersonId], d: Term[DocumentId]) =>
            Sharing.access(invite(lib, t, by, to, what, level), t, p, d) === Sharing.access(lib, t, p, d)))) &&
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
      accept(lib, t, p, what) =!= lib implies
        lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
    after(events).library.invitations.forall(i => isOpen(i, after(events).now - housekeepingWithin)))
    .refines(accessFollowsShares)

  /** The invitations, less any of `to` to `what`. */
  val invitationsWithout = define { (is: Term[List[Invitation]], to: Term[PersonId], what: Term[Target]) =>
    is.filter(i => !(i.to === to && i.what === what)) }

  val inviteContract = Node.claim("Someone who may edit a document or folder invites a person to it at a level: the " +
      "invitation, sent now, takes the place of any earlier invitation of them to it. When anyone else asks, nothing " +
      "changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target],
        level: Term[Level]) => invite(lib, t, by, to, what, level) === when(mayEdit(lib, t, by, what))(
      lib.updated(_.invitations, make[Invitation](to, what, level, by, t) :: invitationsWithout(lib.invitations, to,
        what))).otherwise(lib)))
    .refines(invitationsAreOffers)

  val inviteCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId],
      what: Term[Target], level: Term[Level]) =>
    when(mayEdit(lib, t, by, what))(lib.updated(_.invitations,
      make[Invitation](to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))).otherwise(lib) }

  val acceptContract = Node.claim("A person accepts their open invitation to a document or folder: they then have a " +
      "share of it at the invitation's level, in place of any share of it they had, and the invitation goes. Without " +
      "an open invitation, or when the document is their own (their share of it is the owner's), nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
      accept(lib, t, p, what) ===
        lib.invitations.firstWhere(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
          when(ownedBy(lib, what, make[Grantee.Person](p)))(lib).otherwise(lib
            .updated(_.shares, make[Share](what, make[Grantee.Person](p), i.level, none[BigInt]) ::
              sharesWithout(lib.shares, what, make[Grantee.Person](p)))
            .updated(_.invitations, invitationsWithout(lib.invitations, p, what))))))
    .refines(invitationsAreOffers)

  val acceptCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    val person = make[Grantee.Person](p)
    lib.invitations.firstWhere(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      when(ownedBy(lib, what, person))(lib).otherwise(lib
        .updated(_.shares, make[Share](what, person, i.level, none[BigInt]) :: sharesWithout(lib.shares, what, person))
        .updated(_.invitations, invitationsWithout(lib.invitations, p, what)))) }

  val withdrawContract = Node.claim("Someone who may edit a document or folder withdraws a person's invitation to " +
      "it: the invitation goes. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      withdraw(lib, t, by, to, what) === when(mayEdit(lib, t, by, what))(
        lib.updated(_.invitations, invitationsWithout(lib.invitations, to, what))).otherwise(lib)))
    .refines(invitationsAreOffers)

  val withdrawCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      when(mayEdit(lib, t, by, what))(lib.updated(_.invitations, invitationsWithout(lib.invitations, to, what)))
        .otherwise(lib) }
