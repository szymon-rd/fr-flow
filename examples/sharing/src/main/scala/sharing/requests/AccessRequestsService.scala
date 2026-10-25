package sharing.requests

import sharing.knowledge
import sharing.domain.*

/** Access requests as plain Scala: each method runs its proven code. */
object AccessRequestsService extends AccessRequests:
  private lazy val askRun = knowledge.service(AccessRequests.askContract)()
  private lazy val approveRun = knowledge.service(AccessRequests.approveContract)()
  private lazy val declineRun = knowledge.service(AccessRequests.declineContract)()
  private lazy val chaseRun = knowledge.service(AccessRequests.chaseContract)()

  def ask(library: Library, now: BigInt, person: PersonId, what: Target, level: Level) = askRun(library, now, person, what, level)
  def approve(library: Library, now: BigInt, by: PersonId, person: PersonId, what: Target) = approveRun(library, now, by, person, what)
  def decline(library: Library, now: BigInt, by: PersonId, person: PersonId, what: Target) = declineRun(library, now, by, person, what)
  def chase(library: Library, now: BigInt) = chaseRun(library, now)
