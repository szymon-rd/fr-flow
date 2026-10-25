package sharing

import sharing.domain.*

/** The service as IDEA.md says it, written for the tests apart from the model: folders by their parent (the tree),
  * documents by the folder they are in, "inside" found by walking up the tree, and the clock read at each call. It
  * shares only the data types with the service.
  */
final class Oracle(start: Library):
  private val week = BigInt(7 * 86400)
  private val month = BigInt(30 * 86400)
  private var parentOf: Map[FolderId, Option[FolderId]] = start.folders.map(f => f.id -> f.folders.lastOption).toMap
  private var folderOf: Map[DocumentId, Option[FolderId]] = start.documents.map(d => d.id -> d.folders.lastOption).toMap
  private var trashedAt: Map[DocumentId, BigInt] = start.documents.flatMap(d => d.trashed.map(d.id -> _)).toMap
  private val members: Map[TeamId, Set[PersonId]] = start.teams.map(t => t.id -> t.members.toSet).toMap
  private var shares: List[Share] = start.shares
  /** Pending invitations: to whom, to what, at which level, when sent. */
  private var invited: List[Invitation] = start.invitations
  private var ownerOf: Map[DocumentId, PersonId] = start.documents.map(d => d.id -> d.owner).toMap
  /** Pending access requests, and the notices sent so far (to whom, of what kind). */
  private var asking: List[AccessRequest] = start.requests
  private var told: List[(PersonId, String)] = Nil
  def notices: List[(PersonId, String)] = told.reverse
  private val twoDays = BigInt(2 * 86400)

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

  /** A share gives access until its end, whether or not housekeeping removed it. */
  private def live(s: Share, now: BigInt) = s.until.forall(now < _)
  private def canEdit(now: BigInt, p: PersonId, t: Target) =
    shares.exists(s => live(s, now) && reaches(s, p) && covers(s, t) && s.level == Level.Edit)
  private def gone(d: DocumentId, now: BigInt) = trashedAt.get(d).exists(_ + month <= now)

  def access(now: BigInt, p: PersonId, d: DocumentId): Option[Level] =
    if trashedAt.contains(d) then None
    else
      val mine = shares.filter(s => live(s, now) && reaches(s, p) && covers(s, Target.Doc(d)))
      if mine.exists(_.level == Level.Edit) then Some(Level.Edit) else mine.headOption.map(_ => Level.View)

  private def owners(what: Target, withWhom: Grantee): Boolean = what match
    case Target.Doc(d) => ownerOf.get(d).exists(o => withWhom == Grantee.Person(o))
    case _             => false

  /** Anyone who can edit a document or folder shares it; sharing again with the same person or team replaces the share,
    * except an owner's own share of their document, which stays.
    */
  def share(now: BigInt, by: PersonId, what: Target, withWhom: Grantee, level: Level, until: Option[BigInt]): Boolean =
    canEdit(now, by, what) && !owners(what, withWhom) && {
      shares = Share(what, withWhom, level, until) :: shares.filterNot(s => s.what == what && s.withWhom == withWhom); true
    }

  /** An owner's own share of their document is never unshared. */
  def unshare(now: BigInt, by: PersonId, what: Target, withWhom: Grantee): Boolean =
    canEdit(now, by, what) && !owners(what, withWhom) && { shares = shares.filterNot(s => s.what == what && s.withWhom == withWhom); true }

  /** Moving a document into a folder needs edit on both; out of every folder, edit on the document. */
  def move(now: BigInt, by: PersonId, d: DocumentId, into: Option[FolderId]): Boolean =
    val allowed = canEdit(now, by, Target.Doc(d)) && into.forall(f => parentOf.contains(f) && canEdit(now, by, Target.InFolder(f)))
    if allowed && folderOf.contains(d) then folderOf = folderOf.updated(d, into)
    allowed

  /** An editor invites a person; inviting again renews the invitation. No access until accepted. */
  def invite(now: BigInt, by: PersonId, to: PersonId, what: Target, level: Level): Boolean =
    canEdit(now, by, what) && {
      invited = Invitation(to, what, level, by, now) :: invited.filterNot(i => i.to == to && i.what == what)
      told = (to, "invited") :: told
      true
    }

  /** Accepting within 7 days of the sending makes the share. */
  def accept(now: BigInt, p: PersonId, what: Target): Boolean =
    invited.find(i => i.to == p && i.what == what && now < i.sent + week) match
      case Some(i) =>
        told = invited.filter(j => j.to == p && j.what == what).map(j => (j.by, "accepted")).reverse ++ told
        shares = Share(what, Grantee.Person(p), i.level, None) :: shares.filterNot(s => s.what == what && s.withWhom == Grantee.Person(p))
        invited = invited.filterNot(j => j.to == p && j.what == what)
        true
      case None => false

  def withdraw(now: BigInt, by: PersonId, to: PersonId, what: Target): Boolean =
    canEdit(now, by, what) && { invited = invited.filterNot(i => i.to == to && i.what == what); true }

  /** Deleting puts a document in the trash; one already there keeps its time. */
  def trash(now: BigInt, by: PersonId, d: DocumentId): Boolean =
    canEdit(now, by, Target.Doc(d)) && {
      if folderOf.contains(d) && !trashedAt.contains(d) then trashedAt = trashedAt.updated(d, now)
      true
    }

  /** An editor restores a document in the trash for 30 days. */
  def restore(now: BigInt, by: PersonId, d: DocumentId): Boolean =
    val ok = canEdit(now, by, Target.Doc(d)) && trashedAt.contains(d) && !gone(d, now)
    if ok then trashedAt = trashedAt.removed(d)
    ok

  /** Anyone asks for a document that exists; asking again renews the request. The owner is told. */
  def ask(now: BigInt, p: PersonId, d: DocumentId, level: Level): Boolean =
    ownerOf.contains(d) && {
      asking = AccessRequest(p, d, level, now, false) :: asking.filterNot(r => r.person == p && r.doc == d)
      told = (ownerOf(d), "asked") :: told
      true
    }

  /** An editor approves a pending request (made less than 7 days ago): the share is made, the person told. */
  def approve(now: BigInt, by: PersonId, p: PersonId, d: DocumentId): Boolean =
    asking.find(r => r.person == p && r.doc == d && now < r.asked + week) match
      case Some(r) if canEdit(now, by, Target.Doc(d)) =>
        shares = Share(Target.Doc(d), Grantee.Person(p), r.level, None) ::
          shares.filterNot(s => s.what == Target.Doc(d) && s.withWhom == Grantee.Person(p))
        asking = asking.filterNot(q => q.person == p && q.doc == d)
        told = (p, "approved") :: told
        true
      case _ => false

  def decline(now: BigInt, by: PersonId, p: PersonId, d: DocumentId): Boolean =
    canEdit(now, by, Target.Doc(d)) && {
      asking = asking.filterNot(q => q.person == p && q.doc == d)
      told = (p, "declined") :: told
      true
    }

  /** The owner, while they may edit it, hands a document on to someone who may edit it, who gets an edit share. */
  def transfer(now: BigInt, by: PersonId, d: DocumentId, to: PersonId): Boolean =
    ownerOf.get(d).contains(by) && canEdit(now, by, Target.Doc(d)) && canEdit(now, to, Target.Doc(d)) && {
      ownerOf = ownerOf.updated(d, to)
      shares = Share(Target.Doc(d), Grantee.Person(to), Level.Edit, None) ::
        shares.filterNot(s => s.what == Target.Doc(d) && s.withWhom == Grantee.Person(to))
      told = (to, "handed on") :: told
      true
    }

  def requests: List[AccessRequest] = asking

  /** Housekeeping: what has ended goes; a document 30 days in the trash goes with its shares; a request 7 days old is
    * declined (the person told), one 48 hours old is reminded of once (the owner told).
    */
  def housekeep(now: BigInt): Unit =
    val purged = trashedAt.keySet.filter(gone(_, now))
    shares = shares.filter(s => live(s, now) && !s.what.match { case Target.Doc(d) => purged(d); case _ => false })
    invited = invited.filter(i => now < i.sent + week)
    folderOf = folderOf -- purged
    trashedAt = trashedAt -- purged
    ownerOf = ownerOf -- purged
    val lapsed = asking.filterNot(r => now < r.asked + week)
    val due = asking.filter(r => now < r.asked + week && r.asked + twoDays <= now && !r.reminded)
    told = due.flatMap(r => ownerOf.get(r.doc).map(o => (o, "reminded"))).reverse ++ lapsed.map(r => (r.person, "lapsed")).reverse ++ told
    asking = asking.filter(r => now < r.asked + week).map(r => if due.contains(r) then r.copy(reminded = true) else r)
