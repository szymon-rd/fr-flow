package sharing

import frflow.*
import sharing.domain.*
import sharing.features.Housekeeping
import sharing.features.Invitations
import sharing.features.Ownership
import sharing.features.AccessRequests
import sharing.features.Sharing
import sharing.time.Lifetimes.{gone, inForce, isOpen}
import sharing.features.Trash

// Sharing's nodes in the three kinds (owner §15), each named as today's: the purpose, over its Declarations; the
// claims at the bottom saying what each Declaration is, the code standing in them (2.7); and the claim of each of the
// code's words' equation, proven of the define in `Purpose.scala` that gives the Definition its meaning (as today's
// contracts and their code).

// ============================================================================
// The purpose: no clock and no durations in it
// ============================================================================

val accessFollowsShares = Node.claim("At any moment, a person can view a document exactly when it is not in the " +
    "trash and a share in force lets them view it, and edit it exactly when that share is an edit share; and what is " +
    "shared, offered or kept changes only at the hand of someone who may edit it, of a person taking up an open " +
    "invitation, or of housekeeping clearing away what has ended.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, t, p, d) === (!inTheTrash(lib, d) && mayView(lib, t, p, make[Target.Doc](d))) &&
      Sharing.canEdit(lib, t, p, d) === (!inTheTrash(lib, d) && allowedToEdit(lib, t, p, make[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    Sharing.share(lib, t, by, s) =!= lib implies allowedToEdit(lib, t, by, s.what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    Sharing.unshare(lib, t, by, what, withWhom) =!= lib implies allowedToEdit(lib, t, by, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    Sharing.move(lib, t, by, d, into) =!= lib implies (allowedToEdit(lib, t, by, make[Target.Doc](d)) &&
      into.forall(f => allowedToEdit(lib, t, by, make[Target.InFolder](f))))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    (Invitations.withdraw(lib, t, by, to, what) =!= lib implies allowedToEdit(lib, t, by, what)) &&
      forall((level: Term[Level]) =>
        Invitations.invite(lib, t, by, to, what, level) =!= lib implies allowedToEdit(lib, t, by, what))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    Invitations.accept(lib, t, p, what) =!= lib implies
      lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (Trash.trash(lib, t, by, d) =!= lib implies allowedToEdit(lib, t, by, make[Target.Doc](d))) &&
      (Trash.restore(lib, t, by, d) =!= lib implies allowedToEdit(lib, t, by, make[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    AccessRequests.ask(lib, t, p, w, level).shares === lib.shares &&
      AccessRequests.ask(lib, t, p, w, level).invitations === lib.invitations &&
      AccessRequests.ask(lib, t, p, w, level).documents === lib.documents) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (AccessRequests.approve(lib, t, by, p, w) =!= lib implies allowedToEdit(lib, t, by, w)) &&
      (AccessRequests.decline(lib, t, by, p, w) =!= lib implies allowedToEdit(lib, t, by, w))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    Ownership.transfer(lib, t, by, d, to) =!= lib implies allowedToEdit(lib, t, by, make[Target.Doc](d))) &&
  forall((lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.forall(s => Housekeeping.tidy(lib, t).shares.contains(s) || !inForce(s, t) ||
      lib.documents.exists(doc => gone(doc, t) && s.what === make[Target.Doc](doc.id))) &&
    lib.invitations.forall(i => Housekeeping.tidy(lib, t).invitations.contains(i) || !isOpen(i, t)) &&
    lib.documents.forall(doc => Housekeeping.tidy(lib, t).documents.contains(doc) || gone(doc, t))))

// ============================================================================
// The words, each one equation, proven of its code
// ============================================================================

val reach = Node.claim("A share reaches the person it is with, and everyone in the team it is with.")(
  forall((lib: Term[Library], s: Term[Share], p: Term[PersonId]) => reaches(lib, s, p) ===
    s.withWhom.on[Grantee.Person](q => q === p)
      .on[Grantee.Team](t => lib.teams.exists(team => team.id === t && team.members.contains(p)))))
  .refines(accessFollowsShares)

val cover = Node.claim("A share of a document covers that document; a share of a folder covers the folder, every " +
    "folder inside it, and every document inside any of them.")(
  forall((lib: Term[Library], s: Term[Share], t: Term[Target]) => covers(lib, s, t) ===
    s.what.on[Target.Doc](d => t === make[Target.Doc](d))
      .on[Target.InFolder](f => t
        .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
        .on[Target.InFolder](g =>
          g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f))))))
  .refines(accessFollowsShares)

/** What a person may view: today's `permission`, its first word; a Declaration, said in terms of the code. */
val permission = Node.claim("A person may view a document or folder when a share in force reaches them and covers " +
    "it.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    mayView(lib, t, p, x) === lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x))))
  .refines(accessFollowsShares, sharing.auditTrail)

/** What a person may edit, as the purpose says it: today's `permission`, its second word, in terms of the code. */
val whoMayEdit = Node.claim("A person may edit a document or folder when a share in force that reaches them and " +
    "covers it is an edit share.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    allowedToEdit(lib, t, p, x) ===
      lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit)))
  .refines(accessFollowsShares)

/** What is in the trash, as the purpose says it: today's `inTrash`, in terms of the code. */
val whatIsTrashed = Node.claim("A document is in the trash when it was put there and not restored since.")(
  forall((lib: Term[Library], d: Term[DocumentId]) =>
    inTheTrash(lib, d) === lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined)))
  .refines(accessFollowsShares)

/** What the code lets a person edit: the code's word for today's `permission`'s second, which the code calls. */
val editPermission = Node.claim("The code lets a person edit a document or folder when a share in force that " +
    "reaches them and covers it is an edit share.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    mayEdit(lib, t, p, x) ===
      lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit)))
  .refines(accessFollowsShares)

/** The claim on the code's `inTrash`, in an object of its own: named as its word, it would hide the Definition. */
object Definitions:
  val inTrash = Node.claim("The code holds a document in the trash when it was put there and not restored since.")(
    forall((lib: Term[Library], d: Term[DocumentId]) =>
      sharing.inTrash(lib, d) === lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined)))
    .refines(accessFollowsShares, sharing.invitationsAreOffers)

val ownersShare = Node.claim("An owner's share of a document is a share of it with the document's owner in person.")(
  forall((lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) === what
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === make[Grantee.Person](doc.owner)))
      .on[Target.InFolder](_ => False)))
  .refines(accessFollowsShares)

