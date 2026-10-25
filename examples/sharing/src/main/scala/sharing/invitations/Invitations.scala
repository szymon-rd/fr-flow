package sharing.invitations

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen

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

  val invite = Param[(Library, BigInt, PersonId, PersonId, Target, Level) => Library]("invite", "the library after someone asks to invite a person")
  val accept = Param[(Library, BigInt, PersonId, Target) => Library]("accept", "the library after a person asks to accept an invitation")
  val withdraw = Param[(Library, BigInt, PersonId, PersonId, Target) => Library]("withdraw", "the library after someone asks to withdraw an invitation")

  /** The invitations, less any of `to` to `what`. */
  val invitationsWithout = define { (is: Term[List[Invitation]], to: Term[PersonId], what: Term[Target]) =>
    is.filterNot(i => i.to === to && i.what === what)
  }

  private val withCat = library.copy(invitations = List(catInvited))

  val inviteContract = Node.contract(invite)("InviteContract",
    "Someone who may edit a document or folder invites a person to it at a level: the invitation, sent now, takes the place of any earlier invitation of them to it. When anyone else asks, nothing changes.",
    why = "Q7: an invitation is how someone gets a share they have not asked for yet; inviting is offering a share, which only someone who may share it does. One invitation per person and thing, so inviting again renews it.",
    idea = "Invitations"
  )((lib, t, by, to, what, level, result) =>
    result === mayEdit(lib, t, by, what).fold(
      lib.copy((invitations = Invitation(to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))), lib))
    .under(accessFollowsShares)
    .examples()(
      expect(library, now - day, ann, cat, Target.Doc(plan), Level.View, withCat, "Ann may edit the plan: she invites Cat to view it"),
      expect(library, now, bob, cat, Target.Doc(plan), Level.View, library, "Bob may not edit the plan: nothing changes"),
      reject(library, now, bob, cat, Target.InFolder(reports), Level.View,
        library.copy(invitations = List(Invitation(cat, Target.InFolder(reports), Level.View, bob, now))),
        "Bob may only view the reports folder, so he cannot invite anyone to it"))

  val inviteCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target], level: Term[Level]) =>
    mayEdit(lib, t, by, what).fold(lib.copy((invitations = Invitation(to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))), lib)
  }

  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)

  val acceptContract = Node.contract(accept)("AcceptContract",
    "A person accepts their open invitation to a document or folder: they then have a share of it at the invitation's level, in place of any share of it they had, and the invitation goes. Without an open invitation, nothing changes.",
    why = "Q7: an invitation gives no access until it is accepted, and only while it is open; accepting is what makes the share.",
    idea = "Invitations"
  )((lib, t, p, what, result) =>
    result === lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      lib.copy((shares = Share(what, Grantee[Grantee.Person](p), i.level, none[BigInt]) :: sharesWithout(lib.shares, what, Grantee[Grantee.Person](p)),
        invitations = invitationsWithout(lib.invitations, p, what)))))
    .under(accessFollowsShares)
    .examples()(
      expect(withCat, now, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares),
        "Cat accepts Ann's invitation, sent a day ago: she may view the plan"),
      expect(withCat, now + 7 * day, cat, Target.Doc(plan), withCat, "eight days after it was sent the invitation has lapsed"),
      expect(withCat, now, bob, Target.Doc(plan), withCat, "Bob was not invited"),
      reject(withCat, now + 7 * day, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares),
        "a lapsed invitation is never accepted"))

  val acceptCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      lib.copy((shares = Share(what, Grantee[Grantee.Person](p), i.level, none[BigInt]) :: sharesWithout(lib.shares, what, Grantee[Grantee.Person](p)),
        invitations = invitationsWithout(lib.invitations, p, what))))
  }

  val withdrawContract = Node.contract(withdraw)("WithdrawContract",
    "Someone who may edit a document or folder withdraws a person's invitation to it: the invitation goes. When anyone else asks, nothing changes.",
    why = "Q7: an editor can take an offer back before it is accepted.",
    idea = "Invitations"
  )((lib, t, by, to, what, result) =>
    result === mayEdit(lib, t, by, what).fold(lib.copy((invitations = invitationsWithout(lib.invitations, to, what))), lib))
    .under(accessFollowsShares)
    .examples()(
      expect(withCat, now, ann, cat, Target.Doc(plan), library, "Ann withdraws Cat's invitation"),
      expect(withCat, now, bob, cat, Target.Doc(plan), withCat, "Bob may not edit the plan: the invitation stays"),
      reject(withCat, now, bob, cat, Target.Doc(plan), library, "only an editor withdraws an invitation"))

  val withdrawCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    mayEdit(lib, t, by, what).fold(lib.copy((invitations = invitationsWithout(lib.invitations, to, what))), lib)
  }
