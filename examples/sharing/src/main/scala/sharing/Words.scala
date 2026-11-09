package sharing

import frflow.*
import sharing.domain.*
import sharing.time.Lifetimes.inForce

// The words the purpose is stated in, each one equation: what the purpose's Declarations are, in terms of the code
// standing in them (2.7), and the claim of each of the code's words, proven of the define in `Purpose.scala` that
// gives the Definition its meaning.

val reach = Node.claim("A share reaches the person it is with or, when it is with a team, everyone in the team.")(
  forall((lib: Term[Library], s: Term[Share], p: Term[PersonId]) => reaches(lib, s, p) ===
    s.withWhom.on[Grantee.Person](q => q === p)
      .on[Grantee.Team](t => lib.teams.exists(team => team.id === t && team.members.contains(p)))))
  .refines(viewFollowsShares, editFollowsShares)

val cover = Node.claim("A share covers what it is of and, when that is a folder, every folder and document inside " +
    "it.")(
  forall((lib: Term[Library], s: Term[Share], t: Term[Target]) => covers(lib, s, t) ===
    s.what.on[Target.Doc](d => t === make[Target.Doc](d))
      .on[Target.InFolder](f => t
        .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && doc.folders.contains(f)))
        .on[Target.InFolder](g =>
          g === f || lib.folders.exists(folder => folder.id === g && folder.folders.contains(f))))))
  .refines(viewFollowsShares, editFollowsShares)

/** What a person may view: today's `permission`, its first word; a Declaration, said in terms of the code. */
val permission = Node.claim("A person may view a document or folder when a share in force reaches them and covers " +
    "it.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    mayView(lib, t, p, x) === lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x))))
  .refines(viewFollowsShares, sharing.viewingRestsOnTheLog)

/** What a person may edit, as the purpose says it: today's `permission`, its second word, in terms of the code. */
val whoMayEdit = Node.claim("A person may edit a document or folder when a share in force that reaches them and " +
    "covers it is an edit share.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], x: Term[Target]) =>
    allowedToEdit(lib, t, p, x) ===
      lib.shares.exists(s => inForce(s, t) && reaches(lib, s, p) && covers(lib, s, x) && s.level === Level.Edit)))
  .refines(accessFollowsShares, editFollowsShares)

/** What is in the trash, as the purpose says it: today's `inTrash`, in terms of the code. */
val whatIsTrashed = Node.claim("A document is in the trash when it was put there and not restored since.")(
  forall((lib: Term[Library], d: Term[DocumentId]) =>
    inTheTrash(lib, d) === lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined)))
  .refines(viewFollowsShares, editFollowsShares)

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
    .refines(viewFollowsShares, editFollowsShares, sharing.invitingGivesNoAccess, sharing.invitationsAreOffers)

val ownersShare = Node.claim("An owner's share of a document is a share of it with the document's owner in person.")(
  forall((lib: Term[Library], what: Term[Target], withWhom: Term[Grantee]) =>
    ownedBy(lib, what, withWhom) === what
      .on[Target.Doc](d => lib.documents.exists(doc => doc.id === d && withWhom === make[Grantee.Person](doc.owner)))
      .on[Target.InFolder](_ => False)))
  .refines(sharing.ownersKeepTheirDocuments)
