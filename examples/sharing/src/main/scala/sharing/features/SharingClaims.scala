package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Sharing.*
import sharing.time.Lifetimes.inForce

/** Sharing's claims: what its code is proven to do, each refining a branch or the purpose. */
object SharingClaims:
  val accessContract = Node.claim("A person's access to a document is none while it is in the trash, and otherwise " +
      "the strongest level among the shares in force with them or one of their teams, of the document or a folder " +
      "around it.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) => access(lib, t, p, d) ===
      when(inTrash(lib, d))(none[Level]).otherwise(strongest(lib.shares.filter(s => inForce(s, t) &&
        granteesOf(lib, p).contains(s.withWhom) && placesOf(lib, d).contains(s.what))))))
    .refines(viewFollowsShares, editFollowsShares, sharing.invitingGivesNoAccess)

  val canViewContract = Node.claim("A person can view a document exactly when they have some access to it.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canView(lib, t, p, d) === access(lib, t, p, d).isDefined))
    .refines(viewFollowsShares)

  val canEditContract = Node.claim("A person can edit a document exactly when their access to it is edit.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canEdit(lib, t, p, d) === (access(lib, t, p, d) === some(Level.Edit: Term[Level]))))
    .refines(editFollowsShares)

  val shareContract = Node.claim("Sharing, asked by someone who may edit and not of an owner's own share, puts the " +
      "new share in place of any earlier share of the same with the same person or team, and otherwise changes " +
      "nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) => share(lib, t, by, s) ===
      when(mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom))(
        lib.updated(_.shares, s :: sharesWithout(lib.shares, s.what, s.withWhom))).otherwise(lib)))
    .refines(onlyEditorsShare, sharing.nobodyReplacesAnOwner)

  val unshareContract = Node.claim("Unsharing, asked by someone who may edit and not of an owner's own share, takes " +
      "that share away, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      unshare(lib, t, by, what, withWhom) === when(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom))(
        lib.updated(_.shares, sharesWithout(lib.shares, what, withWhom))).otherwise(lib)))
    .refines(onlyEditorsUnshare, sharing.nobodyUnsharesAnOwner)

  val moveContract = Node.claim("Moving a document, asked by someone who may edit it and the folder it goes into, " +
      "puts it in that folder and every folder around it, or out of every folder, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId],
        into: Term[Option[FolderId]]) => move(lib, t, by, d, into) === when(mayMove(lib, t, by, d, into))(
      lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d)(doc.updated(_.folders, foldersAt(lib, into))).otherwise(doc)))).otherwise(lib)))
    .refines(onlyEditorsMove)
