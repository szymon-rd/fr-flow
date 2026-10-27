package sharing.service

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.inForce

/** Sharing's operations: for each, its claim and its code. Each is a function of the library and of the moment it is
  * asked at; the effects (keeping the library, reading the clock, answering requests) are `sharing.http`'s.
  */
object Sharing:
  val access = Definition[(Library, BigInt, PersonId, DocumentId) => Option[Level]](
    "a person's access to a document at a moment, as the service works it out")
  val canView = Definition[(Library, BigInt, PersonId, DocumentId) => Boolean](
    "the service's answer to whether a person can view a document")
  val canEdit = Definition[(Library, BigInt, PersonId, DocumentId) => Boolean](
    "the service's answer to whether a person can edit a document")
  val share = Definition[(Library, BigInt, PersonId, Share) => Library](
    "the library after someone asks to share a document or folder")
  val unshare = Definition[(Library, BigInt, PersonId, Target, Grantee) => Library](
    "the library after someone asks to unshare a document or folder")
  val move = Definition[(Library, BigInt, PersonId, DocumentId, Option[FolderId]) => Library](
    "the library after someone asks to move a document")

  // ---------------------------------------------------------------------------
  // access: worked out from the person's teams and the document's folders
  // ---------------------------------------------------------------------------

  /** Who a share must be with to reach the person: the person, or one of the teams they are in. */
  val granteesOf = define { (lib: Term[Library], p: Term[PersonId]) =>
    make[Grantee.Person](p) :: lib.teams.filter(t => t.members.contains(p)).mapped(t => make[Grantee.Team](t.id)) }
  /** What a share must be of to cover the document: the document, or one of the folders around it. */
  val placesOf = define { (lib: Term[Library], d: Term[DocumentId]) =>
    make[Target.Doc](d) :: lib.documents.filter(doc => doc.id === d)
      .flatMapped(doc => doc.folders.mapped(f => make[Target.InFolder](f))) }
  /** The strongest level among some shares: edit if one is an edit share, view if there is any, none otherwise. */
  val strongest = define { (ss: Term[List[Share]]) =>
    when(ss.exists(s => s.level === Level.Edit))(some(Level.Edit: Term[Level]))
      .otherwise(when(ss.isEmpty)(none[Level]).otherwise(some(Level.View: Term[Level]))) }

  /** The shares, less any of `what` with `withWhom`. */
  val sharesWithout = define { (ss: Term[List[Share]], what: Term[Target], withWhom: Term[Grantee]) =>
    ss.filter(s => !(s.what === what && s.withWhom === withWhom)) }

  val accessContract = Node.claim("A person's access to a document not in the trash is worked out from their teams " +
      "and the document's folders: among the shares in force with them or one of their teams, of the document or one " +
      "of the folders around it, it is edit if one is an edit share, view if there is any, and none otherwise. A " +
      "document in the trash gives no access.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) => access(lib, t, p, d) ===
      when(inTrash(lib, d))(none[Level]).otherwise(strongest(lib.shares.filter(s => inForce(s, t) &&
        granteesOf(lib, p).contains(s.withWhom) && placesOf(lib, d).contains(s.what))))))
    .refines(accessFollowsShares, sharing.invitations.Invitations.invitationsAreOffers)

  /** Access, worked out: none in the trash; else the shares in force with the person or one of their teams, of the
    * document or a folder around it; the strongest of them.
    */
  val accessCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    val (grantees, places) = (granteesOf(lib, p), placesOf(lib, d))
    when(inTrash(lib, d))(none[Level]).otherwise(strongest(lib.shares.filter(s =>
      inForce(s, t) && grantees.contains(s.withWhom) && places.contains(s.what)))) }

  // ---------------------------------------------------------------------------
  // canView, canEdit: what the access allows
  // ---------------------------------------------------------------------------

  val canViewContract = Node.claim("A person can view a document exactly when they have some access to it.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canView(lib, t, p, d) === access(lib, t, p, d).isDefined))
    .refines(accessFollowsShares)

  val canViewCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, t, p, d).isDefined }

  val canEditContract = Node.claim("A person can edit a document exactly when their access to it is edit.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
      canEdit(lib, t, p, d) === (access(lib, t, p, d) === some(Level.Edit: Term[Level]))))
    .refines(accessFollowsShares)

  val canEditCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, t, p, d) === some(Level.Edit: Term[Level]) }

  // ---------------------------------------------------------------------------
  // share, unshare, move: changes, made only by someone who may edit what they change
  // ---------------------------------------------------------------------------

  val shareContract = Node.claim("Someone who may edit a document or folder shares it with a person or a team at a " +
      "level, for good or until a time: the new share takes the place of any earlier share of it with them, unless " +
      "it is the owner's share of their own document, which stays. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) => share(lib, t, by, s) ===
      when(mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom))(
        lib.updated(_.shares, s :: sharesWithout(lib.shares, s.what, s.withWhom))).otherwise(lib)))
    .refines(accessFollowsShares, sharing.ownership.Ownership.ownersKeepTheirDocuments)

  val shareCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    when(mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom))(
      lib.updated(_.shares, s :: sharesWithout(lib.shares, s.what, s.withWhom))).otherwise(lib) }

  val unshareContract = Node.claim("Someone who may edit a document or folder unshares it from a person or a team: " +
      "their share of it goes, unless it is the owner's share of their own document. When anyone else asks, nothing " +
      "changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      unshare(lib, t, by, what, withWhom) === when(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom))(
        lib.updated(_.shares, sharesWithout(lib.shares, what, withWhom))).otherwise(lib)))
    .refines(accessFollowsShares, sharing.ownership.Ownership.ownersKeepTheirDocuments)

  val unshareCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      when(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom))(
        lib.updated(_.shares, sharesWithout(lib.shares, what, withWhom))).otherwise(lib) }

  /** Whether `by` may move the document into the folder (or out of every folder): they may edit the document, and the
    * folder exists and they may edit it.
    */
  val mayMove = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
      mayEdit(lib, t, by, make[Target.Doc](d)) && into.noneOr(f =>
        lib.folders.exists(folder => folder.id === f) && mayEdit(lib, t, by, make[Target.InFolder](f))) }
  /** The folders a document moved into a folder is in: that folder and the folders around it; none out of every
    * folder.
    */
  val foldersAt = define { (lib: Term[Library], into: Term[Option[FolderId]]) =>
    into.fold(Nil: Term[List[FolderId]])(f => lib.folders.firstWhere(folder => folder.id === f)
      .fold(Nil: Term[List[FolderId]])(folder => folder.folders :+ f)) }

  val moveContract = Node.claim("Someone who may edit a document moves it into a folder they may edit, or out of " +
      "every folder: the document is then in that folder and in every folder around it. When anyone else asks, or " +
      "the folder does not exist, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId],
        into: Term[Option[FolderId]]) => move(lib, t, by, d, into) === when(mayMove(lib, t, by, d, into))(
      lib.updated(_.documents, lib.documents.mapped(doc =>
        when(doc.id === d)(doc.updated(_.folders, foldersAt(lib, into))).otherwise(doc)))).otherwise(lib)))
    .refines(accessFollowsShares)

  val moveCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
      val placed = foldersAt(lib, into)
      when(mayMove(lib, t, by, d, into))(lib.updated(_.documents, lib.documents.mapped(doc =>
        when(doc.id === d)(doc.updated(_.folders, placed)).otherwise(doc)))).otherwise(lib) }
