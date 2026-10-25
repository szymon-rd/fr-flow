package sharing.ownership

import sharing.knowledge
import sharing.domain.*

/** Ownership as plain Scala: its proven code. */
object OwnershipService extends Ownership:
  private lazy val transferRun = knowledge.service(Ownership.transferContract)()
  def transfer(library: Library, now: BigInt, by: PersonId, doc: DocumentId, to: PersonId) = transferRun(library, now, by, doc, to)
