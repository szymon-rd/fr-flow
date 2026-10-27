package sharing.invitations

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.isOpen

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

  /** The invitations, less any of `to` to `what`. */
  val invitationsWithout = define { (is: Term[List[Invitation]], to: Term[PersonId], what: Term[Target]) =>
    is.filter(i => !(i.to === to && i.what === what)) }

  val inviteCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId],
      what: Term[Target], level: Term[Level]) =>
    when(mayEdit(lib, t, by, what))(lib.updated(_.invitations,
      make[Invitation](to, what, level, by, t) :: invitationsWithout(lib.invitations, to, what))).otherwise(lib) }

  val acceptCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    val person = make[Grantee.Person](p)
    lib.invitations.find(i => i.to === p && i.what === what && isOpen(i, t)).fold(lib)(i =>
      when(ownedBy(lib, what, person))(lib).otherwise(lib
        .updated(_.shares, make[Share](what, person, i.level, none[BigInt]) :: sharesWithout(lib.shares, what, person))
        .updated(_.invitations, invitationsWithout(lib.invitations, p, what)))) }

  val withdrawCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
      when(mayEdit(lib, t, by, what))(lib.updated(_.invitations, invitationsWithout(lib.invitations, to, what)))
        .otherwise(lib) }
