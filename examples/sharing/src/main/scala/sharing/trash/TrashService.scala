package sharing.trash

import sharing.knowledge
import sharing.domain.*

/** The trash as plain Scala: each method runs its proven code. */
object TrashService extends Trash:
  private lazy val trashRun = knowledge.service(Trash.trashContract)()
  private lazy val restoreRun = knowledge.service(Trash.restoreContract)()

  def trash(library: Library, now: BigInt, by: PersonId, doc: DocumentId) = trashRun(library, now, by, doc)
  def restore(library: Library, now: BigInt, by: PersonId, doc: DocumentId) = restoreRun(library, now, by, doc)
