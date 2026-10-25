package sharing

import frflow.*
import sharing.domain.*
import sharing.service.Sharing

// ============================================================================
// The vocabulary the purpose is stated in: what a share reaches and covers, and what that lets a person do
// ============================================================================

val reaches = Param[(Library, Share, PersonId) => Boolean]("reaches", "whether a share reaches a person: it is with them, or with a team they are in")
val covers = Param[(Library, Share, Target) => Boolean]("covers",
  "whether a share covers a document or a folder: it is a share of it, or of a folder around it")
val mayView = Param[(Library, PersonId, Target) => Boolean]("mayView", "whether a person may view a document or folder")
val mayEdit = Param[(Library, PersonId, Target) => Boolean]("mayEdit", "whether a person may edit a document or folder")

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
  "A person may view a document or folder when a share reaches them and covers it; they may edit it when such a share is an edit share.",
  why = "Viewing and editing are the two things a person can do with a document, and editing includes viewing (Q1)."
)(
  mayView := ((lib: Term[Library], p: Term[PersonId], t: Term[Target]) => lib.shares.exists(s => reaches(lib, s, p) && covers(lib, s, t))),
  mayEdit := ((lib: Term[Library], p: Term[PersonId], t: Term[Target]) =>
    lib.shares.exists(s => reaches(lib, s, p) && covers(lib, s, t) && s.level === Level.Edit)))

// ============================================================================
// The purpose
// ============================================================================

val accessFollowsShares = Node.claim("AccessFollowsShares",
  "A person can view a document exactly when they may view it, and edit it exactly when they may edit it; and only someone who may edit a document or folder changes who it is shared with, or moves a document, and only into a folder they may edit.",
  why = "The idea in one sentence: the shares decide who sees and who changes what (Q1, Q2). Both halves are exact: the service answers no more and no less than the shares give, and nobody else changes the shares or where a document is.",
  idea = "Who can see and change what"
)(forall((lib: Term[Library], p: Term[PersonId], d: Term[DocumentId]) =>
    Sharing.canView(lib, p, d) === mayView(lib, p, Target[Target.Doc](d)) &&
    Sharing.canEdit(lib, p, d) === mayEdit(lib, p, Target[Target.Doc](d))) &&
  forall((lib: Term[Library], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee], level: Term[Level]) =>
    (Sharing.share(lib, by, what, withWhom, level) =!= lib ==> mayEdit(lib, by, what)) &&
    (Sharing.unshare(lib, by, what, withWhom) =!= lib ==> mayEdit(lib, by, what))) &&
  forall((lib: Term[Library], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    Sharing.move(lib, by, d, into) =!= lib ==>
      (mayEdit(lib, by, Target[Target.Doc](d)) && into.fold(True)(f => mayEdit(lib, by, Target[Target.InFolder](f))))))
