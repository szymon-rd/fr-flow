package sharing.service

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.*
import sharing.time.Lifetimes.inForce

/** Sharing's claims: what its code is proven to do, each refining a branch or the purpose. */
object SharingClaims:
  val accessContract = Node.claim("A person's access to a document not in the trash is worked out from their teams " +
      "and the document's folders: among the shares in force with them or one of their teams, of the document or one " +
      "of the folders around it, it is edit if one is an edit share, view if there is any, and none otherwise. A " +
      "document in the trash gives no access.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) => access(lib, t, p, d) ===
      when(inTrash(lib, d))(none[Level]).otherwise(strongest(lib.shares.filter(s => inForce(s, t) &&
        granteesOf(lib, p).contains(s.withWhom) && placesOf(lib, d).contains(s.what))))))
    .refines(accessFollowsShares, sharing.invitationsAreOffers)

  val canViewContract = Node.claim("A person can view a document exactly when they have some access to it.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canView(lib, t, p, d) === access(lib, t, p, d).isDefined))
    .refines(accessFollowsShares)

  val canEditContract = Node.claim("A person can edit a document exactly when their access to it is edit.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canEdit(lib, t, p, d) === (access(lib, t, p, d) === some(Level.Edit: Term[Level]))))
    .refines(accessFollowsShares)

  val shareContract = Node.claim("Someone who may edit a document or folder shares it with a person or a team at a " +
      "level, for good or until a time: the new share takes the place of any earlier share of it with them, unless " +
      "it is the owner's share of their own document, which stays. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) => share(lib, t, by, s) ===
      when(mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom))(
        lib.updated(_.shares, s :: sharesWithout(lib.shares, s.what, s.withWhom))).otherwise(lib)))
    .refines(accessFollowsShares, sharing.ownersKeepTheirDocuments)

  val unshareContract = Node.claim("Someone who may edit a document or folder unshares it from a person or a team: " +
      "their share of it goes, unless it is the owner's share of their own document. When anyone else asks, nothing " +
      "changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      unshare(lib, t, by, what, withWhom) === when(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom))(
        lib.updated(_.shares, sharesWithout(lib.shares, what, withWhom))).otherwise(lib)))
    .refines(accessFollowsShares, sharing.ownersKeepTheirDocuments)

  val moveContract = Node.claim("Someone who may edit a document moves it into a folder they may edit, or out of " +
      "every folder: the document is then in that folder and in every folder around it. When anyone else asks, or " +
      "the folder does not exist, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId],
        into: Term[Option[FolderId]]) => move(lib, t, by, d, into) === when(mayMove(lib, t, by, d, into))(
      lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d)(doc.updated(_.folders, foldersAt(lib, into))).otherwise(doc)))).otherwise(lib)))
    .refines(accessFollowsShares)
