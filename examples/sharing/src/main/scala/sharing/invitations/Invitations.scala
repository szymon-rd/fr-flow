package sharing.invitations

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen
import sharing.time.Run.{after, events, housekeepingWithin}

/** Invitations: someone who may edit a document or folder invites a person to it; the person accepts while the
  * invitation is open, and only then has the share. Each method is a function of the library and of the moment.
  */
trait Invitations:
  /** The library after `by` invites `to` to `what` at `level`. */
  def invite(library: Library, now: BigInt, by: PersonId, to: PersonId, what: Target, level: Level): Library
  /** The library after `person` accepts their invitation to `what`. */
  def accept(library: Library, now: BigInt, person: PersonId, what: Target): Library
  /** The library after `by` withdraws the invitation of `to` to `what`. */
  def withdraw(library: Library, now: BigInt, by: PersonId, to: PersonId, what: Target): Library

/** The invitations' contracts, each with its code. */
object Invitations:
  import Demo.*

  val invite = Param[(Library, BigInt, PersonId, PersonId, Target, Level) => Library]("the library after someone asks to invite a person")
  val accept = Param[(Library, BigInt, PersonId, Target) => Library]("the library after a person asks to accept an invitation")
  val withdraw = Param[(Library, BigInt, PersonId, PersonId, Target) => Library]("the library after someone asks to withdraw an invitation")

  /** The branch: what an invitation is. Its parts are the three operations, access (to show an invitation gives none),
    * and, below the timed word "open", the deadline by which housekeeping clears a lapsed one away.
    */
  val invitationsAreOffers = Node.claim("An invitation is an offer from someone who may edit: only they send it or take it back, it gives nobody access, it is taken up only by the person invited while it is open, and housekeeping clears it away within one of its periods of its lapsing.",
    why = "Q7: an invitation is how someone gets a share they have not asked for; it is a share offered, not given, so until it is accepted access is as before. Whether it is open is left open here (Lifetimes); that a lapsed one does not linger is what InvitationsLapseOnTime says with the clock.",
    idea = "Invitations"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    (withdraw(lib, t, by, to, what) =!= lib implies mayEdit(lib, t, by, what)) &&
    forall((level: Term[Level]) => (invite(lib, t, by, to, what, level) =!= lib implies mayEdit(lib, t, by, what)) &&
      forall((p: Term[PersonId], d: Term[DocumentId]) =>
        Sharing.access(invite(lib, t, by, to, what, level), t, p, d) === Sharing.access(lib, t, p, d)))) &&
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
      accept(lib, t, p, what) =!= lib implies lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
    after(events).library.invitations.forall(i => isOpen(i, after(events).now - housekeepingWithin)))
    .refines(accessFollowsShares)

  /** The invitations, less any of `to` to `what`. */
  val invitationsWithout = define { (is: Term[List[Invitation]], to: Term[PersonId], what: Term[Target]) =>
    is.filterNot(i => i.to === to && i.what === what)
  }

  private val withCat = library.copy(invitations = List(catInvited))
  private val annInvited = library.copy(invitations = List(Invitation(ann, Target.Doc(plan), Level.View, bob, now - day)))

  val inviteContract = Node.contract("Someone who may edit a document or folder invites a person to it at a level: the invitation, sent now, takes the place of any earlier invitation of them to it. When anyone else asks, nothing changes.",
    why = "Q7: an invitation is how someone gets a share they have not asked for yet; inviting is offering a share, which only someone who may share it does. One invitation per person and thing, so inviting again renews it.",
    idea = "Invitations"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target], level: Term[Level]) =>
    invite(lib, t, by, to, what, level) === mayEdit(lib, t, by, what).fold(
      lib.copy((invitations = Invitation(to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))), lib)))
    .refines(invitationsAreOffers)
    .examples()(
      allows(library, now - day, ann, cat, Target.Doc(plan), Level.View, withCat, "Ann may edit the plan: she invites Cat to view it"),
      allows(library, now, bob, cat, Target.Doc(plan), Level.View, library, "Bob may not edit the plan: nothing changes"),
      forbids(library, now, bob, cat, Target.InFolder(reports), Level.View,
        library.copy(invitations = List(Invitation(cat, Target.InFolder(reports), Level.View, bob, now))),
        "Bob may only view the reports folder, so he cannot invite anyone to it"))

  val inviteCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target], level: Term[Level]) =>
    mayEdit(lib, t, by, what).fold(lib.copy((invitations = Invitation(to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))), lib)
  }

  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)

  val acceptContract = Node.contract("A person accepts their open invitation to a document or folder: they then have a share of it at the invitation's level, in place of any share of it they had, and the invitation goes. Without an open invitation, or when the document is their own (their share of it is the owner's), nothing changes.",
    why = "Q7: an invitation gives no access until it is accepted, and only while it is open; accepting is what makes the share. Q14: nothing replaces an owner's share of their own document, so an owner invited to it keeps their edit share for good.",
    idea = "Invitations"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    accept(lib, t, p, what) === lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      ownedBy(lib, what, Grantee[Grantee.Person](p)).fold(lib,
        lib.copy((shares = Share(what, Grantee[Grantee.Person](p), i.level, none[BigInt]) :: sharesWithout(lib.shares, what, Grantee[Grantee.Person](p)),
          invitations = invitationsWithout(lib.invitations, p, what)))))))
    .refines(invitationsAreOffers)
    .examples()(
      allows(withCat, now, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares),
        "Cat accepts Ann's invitation, sent a day ago: she may view the plan"),
      allows(withCat, now + 7 * day, cat, Target.Doc(plan), withCat, "eight days after it was sent the invitation has lapsed"),
      allows(withCat, now, bob, Target.Doc(plan), withCat, "Bob was not invited"),
      allows(annInvited, now, ann, Target.Doc(plan), annInvited, "Ann owns the plan: accepting a view invitation to it changes nothing"),
      forbids(withCat, now + 7 * day, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares),
        "a lapsed invitation is never accepted"))

  val acceptCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      ownedBy(lib, what, Grantee[Grantee.Person](p)).fold(lib,
        lib.copy((shares = Share(what, Grantee[Grantee.Person](p), i.level, none[BigInt]) :: sharesWithout(lib.shares, what, Grantee[Grantee.Person](p)),
          invitations = invitationsWithout(lib.invitations, p, what)))))
  }

  val withdrawContract = Node.contract("Someone who may edit a document or folder withdraws a person's invitation to it: the invitation goes. When anyone else asks, nothing changes.",
    why = "Q7: an editor can take an offer back before it is accepted.",
    idea = "Invitations"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    withdraw(lib, t, by, to, what) === mayEdit(lib, t, by, what).fold(lib.copy((invitations = invitationsWithout(lib.invitations, to, what))), lib)))
    .refines(invitationsAreOffers)
    .examples()(
      allows(withCat, now, ann, cat, Target.Doc(plan), library, "Ann withdraws Cat's invitation"),
      allows(withCat, now, bob, cat, Target.Doc(plan), withCat, "Bob may not edit the plan: the invitation stays"),
      forbids(withCat, now, bob, cat, Target.Doc(plan), library, "only an editor withdraws an invitation"))

  val withdrawCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    mayEdit(lib, t, by, what).fold(lib.copy((invitations = invitationsWithout(lib.invitations, to, what))), lib)
  }
