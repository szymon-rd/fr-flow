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

  def access(library: Library, now: BigInt, person: PersonId, doc: DocumentId) = accessRun(library, now, person, doc)
  def canView(library: Library, now: BigInt, person: PersonId, doc: DocumentId) = canViewRun(library, now, person, doc)
  def canEdit(library: Library, now: BigInt, person: PersonId, doc: DocumentId) = canEditRun(library, now, person, doc)
  def share(library: Library, now: BigInt, by: PersonId, share: Share) = shareRun(library, now, by, share)
  def unshare(library: Library, now: BigInt, by: PersonId, what: Target, withWhom: Grantee) = unshareRun(library, now, by, what, withWhom)
  def move(library: Library, now: BigInt, by: PersonId, doc: DocumentId, into: Option[FolderId]) = moveRun(library, now, by, doc, into)
