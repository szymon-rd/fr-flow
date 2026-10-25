package sharing.requests

import sharing.knowledge
import sharing.domain.*

/** Access requests as plain Scala: each method runs its proven code. */
object AccessRequestsService extends AccessRequests:
  private lazy val askRun = knowledge.service(AccessRequests.askContract)()
  private lazy val approveRun = knowledge.service(AccessRequests.approveContract)()
  private lazy val declineRun = knowledge.service(AccessRequests.declineContract)()
  private lazy val chaseRun = knowledge.service(AccessRequests.chaseContract)()

  def ask(library: Library, now: BigInt, person: PersonId, doc: DocumentId, level: Level) = askRun(library, now, person, doc, level)
  def approve(library: Library, now: BigInt, by: PersonId, person: PersonId, doc: DocumentId) = approveRun(library, now, by, person, doc)
  def decline(library: Library, now: BigInt, by: PersonId, person: PersonId, doc: DocumentId) = declineRun(library, now, by, person, doc)
  def chase(library: Library, now: BigInt) = chaseRun(library, now)
