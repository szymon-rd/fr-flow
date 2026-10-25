package sharing

import sharing.domain.*

/** The service as IDEA.md says it, written for the tests apart from the model: folders by their parent (the tree),
  * documents by the folder they are in, and "inside" found by walking up the tree. It shares only the data types with
  * the service.
  */
final class Oracle(start: Library):
  private var parentOf: Map[FolderId, Option[FolderId]] = start.folders.map(f => f.id -> f.folders.lastOption).toMap
  private var folderOf: Map[DocumentId, Option[FolderId]] = start.documents.map(d => d.id -> d.folders.lastOption).toMap
  private val members: Map[TeamId, Set[PersonId]] = start.teams.map(t => t.id -> t.members.toSet).toMap
  private var shares: List[Share] = start.shares

  /** The folders a folder is inside, walking up the tree; the folder itself first. */
  private def upFrom(f: FolderId): List[FolderId] = f :: parentOf.get(f).flatten.fold(Nil)(upFrom)

  private def reaches(s: Share, p: PersonId) = s.withWhom match
    case Grantee.Person(q) => q == p
    case Grantee.Team(t)   => members.get(t).exists(_.contains(p))

  /** A share of a folder covers it and what is inside it at any depth; a share of a document covers that document. */
  private def covers(s: Share, t: Target) = (s.what, t) match
    case (Target.Doc(a), Target.Doc(b))           => a == b
    case (Target.Doc(_), Target.InFolder(_))      => false
    case (Target.InFolder(f), Target.Doc(d))      => folderOf.get(d).flatten.exists(upFrom(_).contains(f))
    case (Target.InFolder(f), Target.InFolder(g)) => parentOf.contains(g) && upFrom(g).contains(f) || f == g

  private def canEdit(p: PersonId, t: Target) = shares.exists(s => reaches(s, p) && covers(s, t) && s.level == Level.Edit)

  def access(p: PersonId, d: DocumentId): Option[Level] =
    val mine = shares.filter(s => reaches(s, p) && covers(s, Target.Doc(d)))
    if mine.exists(_.level == Level.Edit) then Some(Level.Edit) else mine.headOption.map(_ => Level.View)

  /** Anyone who can edit a document or folder shares it; sharing again with the same person or team changes the level. */
  def share(by: PersonId, what: Target, withWhom: Grantee, level: Level): Boolean =
    canEdit(by, what) && { shares = Share(what, withWhom, level) :: shares.filterNot(s => s.what == what && s.withWhom == withWhom); true }

  def unshare(by: PersonId, what: Target, withWhom: Grantee): Boolean =
    canEdit(by, what) && { shares = shares.filterNot(s => s.what == what && s.withWhom == withWhom); true }

  /** Moving a document into a folder needs edit on both; out of every folder, edit on the document. */
  def move(by: PersonId, d: DocumentId, into: Option[FolderId]): Boolean =
    val allowed = canEdit(by, Target.Doc(d)) && into.forall(f => parentOf.contains(f) && canEdit(by, Target.InFolder(f)))
    if allowed && folderOf.contains(d) then folderOf = folderOf.updated(d, into)
    allowed
