package sharing.time

import frflow.*
import sharing.*
import sharing.domain.*

/** How long things last: when a share stops being in force, an invitation stops being open, and a document in the trash
  * is gone. Above this point the service speaks of these words only ("a share in force", "an open invitation", "a
  * document gone"), and is proven for whatever they mean; here they are fixed with the clock.
  */
trait Lifetimes:
  def inForce(share: Share, now: BigInt): Boolean
  def isOpen(invitation: Invitation, now: BigInt): Boolean
  def gone(document: Document, now: BigInt): Boolean

/** The lifetimes' contracts, each with its code, and the durations they are stated with. */
object Lifetimes:
  import Demo.*

  val inForce = Param[(Share, BigInt) => Boolean]("inForce", "whether a share is in force at a moment: it gives access then")
  val isOpen = Param[(Invitation, BigInt) => Boolean]("isOpen", "whether an invitation is open at a moment: it can be accepted then")
  val gone = Param[(Document, BigInt) => Boolean]("gone",
    "whether a document is gone at a moment: past restoring, purged by the next housekeeping")

  // ---------------------------------------------------------------------------
  // the durations
  // ---------------------------------------------------------------------------

  val invitationLasts = Param[BigInt]("invitationLasts", "how long an invitation stays open after it is sent, in seconds")
  val trashKeeps = Param[BigInt]("trashKeeps", "how long a document stays in the trash before it is gone, in seconds")

  val invitationLifetime = Node.definition("InvitationLifetime", "An invitation stays open for 7 days after it is sent.",
    why = "Q7: an invitation lapses after 7 days; a week is long enough to answer, short enough not to leave stale offers."
  )(invitationLasts := (7 * 86400: Term[BigInt]))

  val trashLifetime = Node.definition("TrashLifetime", "A document stays in the trash for 30 days.",
    why = "Q8: a document in the trash can be restored for 30 days, then it is deleted for good."
  )(trashKeeps := (30 * 86400: Term[BigInt]))

  // ---------------------------------------------------------------------------
  // in force, open, gone
  // ---------------------------------------------------------------------------

  val inForceContract = Node.contract(inForce)("InForceContract",
    "A share is in force while now is before its end; a share with no end is always in force.",
    why = "Q6: a share may be given until a time; from that time on it gives no access, whether or not housekeeping has removed it yet, because access reads the clock.",
    idea = "Expiring shares"
  )((s, t, result) => result === s.until.fold(True)(end => t < end))
    .leftOpenAbove
    .under(Deadlines.endedStaysEnded)
    .examples()(
      expect(annEditsPlan, now, true, "a share with no end"),
      expect(bobViewsPlanForAnHour, now, true, "an hour before its end"),
      expect(bobViewsPlanForAnHour, now + 3600, false, "at its end it has ended"),
      reject(bobViewsPlanForAnHour, now + 7200, true, "never after its end"))

  val inForceCode = define { (s: Term[Share], t: Term[BigInt]) => s.until.fold(True)(end => t < end) }

  val isOpenContract = Node.contract(isOpen)("IsOpenContract",
    "An invitation is open from its sending until 7 days after; then it has lapsed.",
    why = "Q7: an invitation lapses after 7 days. Accepting it removes it, so an accepted invitation is no longer pending at all.",
    idea = "Invitations"
  )((i, t, result) => result === (t < i.sent + invitationLasts))
    .leftOpenAbove
    .under(sharing.invitations.Invitations.invitationsAreOffers, Deadlines.invitationsLapseOnTime, Deadlines.endedStaysEnded)
    .examples()(
      expect(catInvited, now, true, "sent a day ago"),
      expect(catInvited, now + 6 * day - 1, true, "a second before seven days have passed"),
      expect(catInvited, now + 6 * day, false, "seven days after it was sent"),
      reject(catInvited, now + 30 * day, true, "a month later it has long lapsed"))

  val isOpenCode = define { (i: Term[Invitation], t: Term[BigInt]) => t < i.sent + invitationLasts }

  val goneContract = Node.contract(gone)("GoneContract",
    "A document in the trash is gone 30 days after it was put there; a document not in the trash is never gone.",
    why = "Q8: the trash keeps a document for 30 days, during which it can be restored; after that it is purged.",
    idea = "Trash"
  )((doc, t, result) => result === doc.trashed.fold(False)(at => at + trashKeeps <= t))
    .leftOpenAbove
    .under(sharing.trash.Trash.trashUntilGone, Deadlines.trashPurgedOnTime, Deadlines.endedStaysEnded)
    .examples()(
      expect(planTrashed, now, false, "trashed a day ago: still restorable"),
      expect(planTrashed, now + 29 * day, true, "thirty days after it was trashed"),
      expect(planDoc, now + 100 * day, false, "not in the trash"),
      reject(planTrashed, now + 28 * day, true, "never before thirty days"))

  val goneCode = define { (doc: Term[Document], t: Term[BigInt]) => doc.trashed.fold(False)(at => at + trashKeeps <= t) }
