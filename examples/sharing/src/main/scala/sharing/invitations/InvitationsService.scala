package sharing.invitations

import sharing.knowledge
import sharing.domain.*

/** Invitations as plain Scala: each method runs its proven code. */
object InvitationsService extends Invitations:
  private lazy val inviteRun = knowledge.service(Invitations.inviteContract)()
  private lazy val acceptRun = knowledge.service(Invitations.acceptContract)()
  private lazy val withdrawRun = knowledge.service(Invitations.withdrawContract)()

  def invite(library: Library, now: BigInt, by: PersonId, to: PersonId, what: Target, level: Level) = inviteRun(library, now, by, to, what, level)
  def accept(library: Library, now: BigInt, person: PersonId, what: Target) = acceptRun(library, now, person, what)
  def withdraw(library: Library, now: BigInt, by: PersonId, to: PersonId, what: Target) = withdrawRun(library, now, by, to, what)
