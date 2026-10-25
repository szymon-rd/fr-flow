package sharing.time

import sharing.knowledge
import sharing.domain.*

/** The lifetimes as plain Scala: each runs its proven code. */
object LifetimesService extends Lifetimes:
  private lazy val inForceRun = knowledge.service(Lifetimes.inForceContract)()
  private lazy val isOpenRun = knowledge.service(Lifetimes.isOpenContract)()
  private lazy val goneRun = knowledge.service(Lifetimes.goneContract)()

  def inForce(share: Share, now: BigInt) = inForceRun(share, now)
  def isOpen(invitation: Invitation, now: BigInt) = isOpenRun(invitation, now)
  def gone(document: Document, now: BigInt) = goneRun(document, now)
