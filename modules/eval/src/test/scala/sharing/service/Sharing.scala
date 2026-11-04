package sharing.service

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
    make[Grantee.Person](p) :: lib.teams.filter(t => t.members.contains(p)).map(t => make[Grantee.Team](t.id)) }
  /** What a share must be of to cover the document: the document, or one of the folders around it. */
  val placesOf = define { (lib: Term[Library], d: Term[DocumentId]) =>
    make[Target.Doc](d) :: lib.documents.filter(doc => doc.id === d)
      .flatMap(doc => doc.folders.map(f => make[Target.InFolder](f))) }
  /** The strongest level among some shares: edit if one is an edit share, view if there is any, none otherwise. */
  val strongest = define { (ss: Term[List[Share]]) =>
    when(ss.exists(s => s.level === Level.Edit))(some(Level.Edit: Term[Level]))
      .otherwise(when(ss.isEmpty)(none[Level]).otherwise(some(Level.View: Term[Level]))) }

  /** The shares, less any of `what` with `withWhom`. */
  val sharesWithout = define { (ss: Term[List[Share]], what: Term[Target], withWhom: Term[Grantee]) =>
    ss.filter(s => !(s.what === what && s.withWhom === withWhom)) }

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

  val canViewCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, t, p, d).isDefined }

  val canEditCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, t, p, d) === some(Level.Edit: Term[Level]) }

  // ---------------------------------------------------------------------------
  // share, unshare, move: changes, made only by someone who may edit what they change
  // ---------------------------------------------------------------------------

  val shareCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    when(mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom))(
      lib.updated(_.shares, s :: sharesWithout(lib.shares, s.what, s.withWhom))).otherwise(lib) }

  val unshareCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      when(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom))(
        lib.updated(_.shares, sharesWithout(lib.shares, what, withWhom))).otherwise(lib) }

  /** Whether `by` may move the document into the folder (or out of every folder): they may edit the document, and the
    * folder exists and they may edit it.
    */
  val mayMove = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
      mayEdit(lib, t, by, make[Target.Doc](d)) && into.forall(f =>
        lib.folders.exists(folder => folder.id === f) && mayEdit(lib, t, by, make[Target.InFolder](f))) }
  /** The folders a document moved into a folder is in: that folder and the folders around it; none out of every
    * folder.
    */
  val foldersAt = define { (lib: Term[Library], into: Term[Option[FolderId]]) =>
    into.fold(Nil: Term[List[FolderId]])(f => lib.folders.find(folder => folder.id === f)
      .fold(Nil: Term[List[FolderId]])(folder => folder.folders :+ f)) }

  val moveCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
      val placed = foldersAt(lib, into)
      when(mayMove(lib, t, by, d, into))(lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d)(doc.updated(_.folders, placed)).otherwise(doc)))).otherwise(lib) }
