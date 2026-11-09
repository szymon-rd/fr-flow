package sharing

import frflow.*
import sharing.domain.*
import sharing.time.Lifetimes.inForce

// The vocabulary sharing's purpose is stated in: what a share reaches and covers, and what that lets a person do. The
// purpose's own words are Declarations (owner §14, §27): whether a person may view or edit a document, and whether a
// document is in the trash, each said by a claim at the bottom in terms of the code (`Root.scala`). The code's words
// are Definitions, each given its meaning by a define here (the same body as the claim of its equation).

val mayView = Declaration[(Library, BigInt, PersonId, Target) => Boolean](
  "whether a person may view a document or folder at a moment")
val allowedToEdit = Declaration[(Library, BigInt, PersonId, Target) => Boolean](
  "whether a person may edit a document or folder at a moment")
val inTheTrash = Declaration[(Library, DocumentId) => Boolean]("whether a document is in the trash")

val reaches = Definition[(Library, Share, PersonId) => Boolean](
  "whether a share reaches a person: it is with them, or with a team they are in")
val covers = Definition[(Library, Share, Target) => Boolean](
  "whether a share covers a document or a folder: it is a share of it, or of a folder around it")
val mayEdit = Definition[(Library, BigInt, PersonId, Target) => Boolean](
  "whether the code lets a person edit a document or folder at a moment")
val inTrash = Definition[(Library, DocumentId) => Boolean]("whether the code holds a document in the trash")
val ownedBy = Definition[(Library, Target, Grantee) => Boolean](
  "whether a share of a document or folder with someone is the owner's share of their own document")

// What gives each its meaning.

val reachesCode = define { (lib: Term[Library], s: Term[Share], p: Term[PersonId]) =>
  s.withWhom.on[Grantee.Person](q => q === p)
    .on[Grantee.Team](t => lib.teams.exists(team => team.id === t && team.members.contains(p))) }

val coversCode = define { (lib: Term[Library], s: Term[Share], t: Term[Target]) =>
  s.what.on[Target.Doc](d => t === make[Target.Doc](d))
    .on[Target.InFolder](f => t
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
      .on[Target.InFolder](g =>
        g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f)))) }

val mayEditCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
  lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit) }

val inTrashCode = define { (lib: Term[Library], d: Term[DocumentId]) =>
  lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined) }

// The ideas the purpose and its branches are stated in, each named once.

/** Whether an operation changed the library: what it leaves is not what it was given. */
val changes = define { (before: Term[Library], after: Term[Library]) => after =!= before }

/** Whether two libraries share, offer and keep the same: the same shares, invitations and documents. */
val sameKept = define { (before: Term[Library], after: Term[Library]) =>
  after.shares === before.shares && after.invitations === before.invitations && after.documents === before.documents }

val ownedByCode = define { (lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
  what.on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === make[Grantee.Person](doc.owner)))
    .on[Target.InFolder](_ => False) }
