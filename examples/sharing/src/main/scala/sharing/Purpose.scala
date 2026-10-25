package sharing

import frflow.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.invitations.Invitations
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.time.Lifetimes.{gone, inForce, isOpen}
import sharing.trash.Trash

// ============================================================================
// The vocabulary the purpose is stated in: what a share reaches and covers, and what that lets a person do. A share
// is "in force", an invitation "open", a document "gone": words this level leaves open (Lifetimes fixes them with the
// clock, below), so what is proven here holds whatever they come to mean.
// ============================================================================

val reaches = Param[(Library, Share, PersonId) => Boolean]("reaches", "whether a share reaches a person: it is with them, or with a team they are in")
val covers = Param[(Library, Share, Target) => Boolean]("covers",
  "whether a share covers a document or a folder: it is a share of it, or of a folder around it")
val mayView = Param[(Library, BigInt, PersonId, Target) => Boolean]("mayView", "whether a person may view a document or folder at a moment")
val mayEdit = Param[(Library, BigInt, PersonId, Target) => Boolean]("mayEdit", "whether a person may edit a document or folder at a moment")
val inTrash = Param[(Library, DocumentId) => Boolean]("inTrash", "whether a document is in the trash")
val ownedBy = Param[(Library, Target, Grantee) => Boolean]("ownedBy", "whether a share of a document or folder with someone is the owner's share of their own document")

val reach = Node.definition("Reach", "A share reaches the person it is with, and everyone in the team it is with.",
  why = "Teams contain people only (Q3), so a share with a team reaches exactly its members, and nobody else."
)(reaches := ((lib: Term[Library], s: Term[Share], p: Term[PersonId]) =>
  s.withWhom
    .on[Grantee.Person](q => q === p)
    .on[Grantee.Team](t => lib.teams.exists(team => team.id === t && team.members.contains(p)))))

val cover = Node.definition("Cover",
  "A share of a document covers that document; a share of a folder covers the folder, every folder inside it, and every document inside any of them.",
  why = "Sharing a folder shares everything inside it, at any depth (Q4). A document or folder is inside a folder when that folder is among the folders around it."
)(covers := ((lib: Term[Library], s: Term[Share], t: Term[Target]) =>
  s.what
    .on[Target.Doc](d => t === Target[Target.Doc](d))
    .on[Target.InFolder](f => t
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
      .on[Target.InFolder](g => g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f))))))

val permission = Node.definition("Permission",
  "A person may view a document or folder when a share in force reaches them and covers it; they may edit it when such a share is an edit share.",
  why = "Viewing and editing are the two things a person can do with a document, and editing includes viewing (Q1). Only a share in force counts: a share that has ended gives nothing (Q6)."
)(
  mayView := ((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x))),
  mayEdit := ((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit)))

val trashed = Node.definition("InTrash", "A document is in the trash when it was put there and not restored since.",
  why = "Q8: a document in the trash gives nobody access, whatever its shares say; restoring it brings them back."
)(inTrash := ((lib: Term[Library], d: Term[DocumentId]) => lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined)))

val owner = Node.definition("OwnersShare", "An owner's share of a document is a share of it with the document's owner in person.",
  why = "Q14: what nobody may unshare is the owner's own share of their document; a share with a team the owner is in is not theirs in person."
)(ownedBy := ((lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
  what
    .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === Grantee[Grantee.Person](doc.owner)))
    .on[Target.InFolder](_ => False)))

// ============================================================================
// The purpose: no clock and no durations in it
// ============================================================================

val accessFollowsShares = Node.claim("AccessFollowsShares",
  "At any moment, a person can view a document exactly when it is not in the trash and a share in force lets them view it, and edit it exactly when that share is an edit share; and what is shared, offered or kept changes only at the hand of someone who may edit it, of a person taking up an open invitation, or of housekeeping clearing away what has ended.",
  why = "The idea in one statement, in two halves as in stage 1: the shares in force decide who sees and who changes what (Q1, Q2), the trash hides a document (Q8); and nothing changes that but an editor, an invitation an editor sent (Q7), or housekeeping removing what gives nothing any more. How invitations, the trash and housekeeping do their part is said in their own branches below. Whether a share is in force, an invitation open or a document gone is left open here: Lifetimes fixes it with the clock below, and this holds whatever it says.",
  idea = "Who can see and change what"
)(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, t, p, d) === (!inTrash(lib, d) && mayView(lib, t, p, Target[Target.Doc](d))) &&
    Sharing.canEdit(lib, t, p, d) === (!inTrash(lib, d) && mayEdit(lib, t, p, Target[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    Sharing.share(lib, t, by, s) =!= lib ==> mayEdit(lib, t, by, s.what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    Sharing.unshare(lib, t, by, what, withWhom) =!= lib ==> mayEdit(lib, t, by, what)) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    Sharing.move(lib, t, by, d, into) =!= lib ==>
      (mayEdit(lib, t, by, Target[Target.Doc](d)) && into.fold(True)(f => mayEdit(lib, t, by, Target[Target.InFolder](f))))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], to: Term[PersonId], what: Term[Target]) =>
    (Invitations.withdraw(lib, t, by, to, what) =!= lib ==> mayEdit(lib, t, by, what)) &&
    forall((level: Term[Level]) => Invitations.invite(lib, t, by, to, what, level) =!= lib ==> mayEdit(lib, t, by, what))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], what: Term[Target]) =>
    Invitations.accept(lib, t, p, what) =!= lib ==> lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (Trash.trash(lib, t, by, d) =!= lib ==> mayEdit(lib, t, by, Target[Target.Doc](d))) &&
    (Trash.restore(lib, t, by, d) =!= lib ==> mayEdit(lib, t, by, Target[Target.Doc](d)))) &&
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    AccessRequests.ask(lib, t, p, w, level).shares === lib.shares && AccessRequests.ask(lib, t, p, w, level).invitations === lib.invitations &&
      AccessRequests.ask(lib, t, p, w, level).documents === lib.documents) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    (AccessRequests.approve(lib, t, by, p, w) =!= lib ==> mayEdit(lib, t, by, w)) &&
    (AccessRequests.decline(lib, t, by, p, w) =!= lib ==> mayEdit(lib, t, by, w))) &&
  forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    Ownership.transfer(lib, t, by, d, to) =!= lib ==> mayEdit(lib, t, by, Target[Target.Doc](d))) &&
  forall((lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.forall(s => Housekeeping.tidy(lib, t).shares.contains(s) || !inForce(s, t) ||
      lib.documents.exists(doc => gone(doc, t) && s.what === Target[Target.Doc](doc.id))) &&
    lib.invitations.forall(i => Housekeeping.tidy(lib, t).invitations.contains(i) || !isOpen(i, t)) &&
    lib.documents.forall(doc => Housekeeping.tidy(lib, t).documents.contains(doc) || gone(doc, t))))
