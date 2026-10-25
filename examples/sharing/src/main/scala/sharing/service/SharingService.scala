package sharing.service

import sharing.knowledge
import sharing.domain.*

/** Sharing as plain Scala: each method runs its code (the `define` beside its contract, proven to meet it); the
  * knowledge base binds the operations that code calls to their own code.
  */
object SharingService extends Sharing:
  private lazy val accessRun = knowledge.service(Sharing.accessContract)()
  private lazy val canViewRun = knowledge.service(Sharing.canViewContract)()
  private lazy val canEditRun = knowledge.service(Sharing.canEditContract)()
  private lazy val shareRun = knowledge.service(Sharing.shareContract)()
  private lazy val unshareRun = knowledge.service(Sharing.unshareContract)()
  private lazy val moveRun = knowledge.service(Sharing.moveContract)()

  def access(library: Library, person: PersonId, doc: DocumentId) = accessRun(library, person, doc)
  def canView(library: Library, person: PersonId, doc: DocumentId) = canViewRun(library, person, doc)
  def canEdit(library: Library, person: PersonId, doc: DocumentId) = canEditRun(library, person, doc)
  def share(library: Library, by: PersonId, what: Target, withWhom: Grantee, level: Level) = shareRun(library, by, what, withWhom, level)
  def unshare(library: Library, by: PersonId, what: Target, withWhom: Grantee) = unshareRun(library, by, what, withWhom)
  def move(library: Library, by: PersonId, doc: DocumentId, into: Option[FolderId]) = moveRun(library, by, doc, into)
