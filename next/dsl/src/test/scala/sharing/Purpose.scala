package sharing

import examples.Folds.*
import frflow.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.invitations.Invitations
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.time.Lifetimes.{gone, inForce, isOpen}
import sharing.trash.Trash

// Sharing's nodes in the three kinds (owner §15), each named as today's. The words the purpose leaves open are
// Definitions code uses: each of today's definition nodes is a claim of its equation, proven of the define that
// gives the Definition its meaning (the same body, as today's contracts and their code). The vocabulary the purpose is stated in: what a share reaches and covers, and what that lets
// a person do.

val reaches = Definition[(Library, Share, PersonId) => Boolean](
  "whether a share reaches a person: it is with them, or with a team they are in")
val covers = Definition[(Library, Share, Target) => Boolean](
  "whether a share covers a document or a folder: it is a share of it, or of a folder around it")
val mayView = Definition[(Library, BigInt, PersonId, Target) => Boolean](
  "whether a person may view a document or folder at a moment")
val mayEdit = Definition[(Library, BigInt, PersonId, Target) => Boolean](
  "whether a person may edit a document or folder at a moment")
val inTrash = Definition[(Library, DocumentId) => Boolean]("whether a document is in the trash")
val ownedBy = Definition[(Library, Target, Grantee) => Boolean](
  "whether a share of a document or folder with someone is the owner's share of their own document")

// ============================================================================
// The purpose: no clock and no durations in it
// ============================================================================

val accessFollowsShares = Node.claim("At any moment, a person can view a document exactly when it is not in the " +
    "trash and a share in force lets them view it, and edit it exactly when that share is an edit share; and what is " +
    "shared, offered or kept changes only at the hand of someone who may edit it, of a person taking up an open " +
    "invitation, or of housekeeping clearing away what has ended.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, t, p, d) === (!inTrash(lib, d) && mayView(lib, t, p, make[Target.Doc](d))) &&
      Sharing.canEdit(lib, t, p, d) === (!inTrash(lib, d) && mayEdit(lib, t, p, make[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    Sharing.share(lib, t, by, s) =!= lib implies mayEdit(lib, t, by, s.what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    Sharing.unshare(lib, t, by, what, withWhom) =!= lib implies mayEdit(lib, t, by, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    Sharing.move(lib, t, by, d, into) =!= lib implies (mayEdit(lib, t, by, make[Target.Doc](d)) &&
      into.noneOr(f => mayEdit(lib, t, by, make[Target.InFolder](f))))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    (Invitations.withdraw(lib, t, by, to, what) =!= lib implies mayEdit(lib, t, by, what)) &&
      forall((level: Term[Level]) =>
        Invitations.invite(lib, t, by, to, what, level) =!= lib implies mayEdit(lib, t, by, what))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    Invitations.accept(lib, t, p, what) =!= lib implies
      lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (Trash.trash(lib, t, by, d) =!= lib implies mayEdit(lib, t, by, make[Target.Doc](d))) &&
      (Trash.restore(lib, t, by, d) =!= lib implies mayEdit(lib, t, by, make[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    AccessRequests.ask(lib, t, p, w, level).shares === lib.shares &&
      AccessRequests.ask(lib, t, p, w, level).invitations === lib.invitations &&
      AccessRequests.ask(lib, t, p, w, level).documents === lib.documents) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (AccessRequests.approve(lib, t, by, p, w) =!= lib implies mayEdit(lib, t, by, w)) &&
      (AccessRequests.decline(lib, t, by, p, w) =!= lib implies mayEdit(lib, t, by, w))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    Ownership.transfer(lib, t, by, d, to) =!= lib implies mayEdit(lib, t, by, make[Target.Doc](d))) &&
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

val reachesCode = define { (lib: Term[Library], s: Term[Share], p: Term[PersonId]) =>
  s.withWhom.on[Grantee.Person](q => q === p)
    .on[Grantee.Team](t => lib.teams.exists(team => team.id === t && team.members.contains(p))) }

val cover = Node.claim("A share of a document covers that document; a share of a folder covers the folder, every " +
    "folder inside it, and every document inside any of them.")(
  forall((lib: Term[Library], s: Term[Share], t: Term[Target]) => covers(lib, s, t) ===
    s.what.on[Target.Doc](d => t === make[Target.Doc](d))
      .on[Target.InFolder](f => t
        .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
        .on[Target.InFolder](g =>
          g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f))))))
  .refines(accessFollowsShares)

val coversCode = define { (lib: Term[Library], s: Term[Share], t: Term[Target]) =>
  s.what.on[Target.Doc](d => t === make[Target.Doc](d))
    .on[Target.InFolder](f => t
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
      .on[Target.InFolder](g => g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f)))) }

val permission = Node.claim("A person may view a document or folder when a share in force reaches them and covers " +
    "it; they may edit it when such a share is an edit share.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    mayView(lib, t, p, x) === lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x)) &&
      mayEdit(lib, t, p, x) ===
        lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit)))
  .refines(accessFollowsShares)

val mayViewCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
  lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x)) }

val mayEditCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
  lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit) }

/** The claim on `inTrash`, in an object of its own: named `inTrash` too, it would hide the Definition. */
object Definitions:
  val inTrash = Node.claim("A document is in the trash when it was put there and not restored since.")(
    forall((lib: Term[Library], d: Term[DocumentId]) =>
      sharing.inTrash(lib, d) === lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined)))
    .refines(accessFollowsShares)

val inTrashCode = define { (lib: Term[Library], d: Term[DocumentId]) =>
  lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined) }

val ownersShare = Node.claim("An owner's share of a document is a share of it with the document's owner in person.")(
  forall((lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) === what
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === make[Grantee.Person](doc.owner)))
      .on[Target.InFolder](_ => False)))
  .refines(accessFollowsShares)

val ownedByCode = define { (lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
  what.on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === make[Grantee.Person](doc.owner)))
    .on[Target.InFolder](_ => False) }
