package sharing.time

import frflow.*
import sharing.domain.*

/** How long things last: when a share stops being in force, an invitation stops being open, and a document in the trash
  * is gone. Above this point the service speaks of these words only, and is proven for whatever they mean; here they
  * are fixed with the clock.
  */
object Lifetimes:
  val inForce = Definition[(Share, BigInt) => Boolean]("whether a share is in force at a moment: it gives access then")
  val isOpen = Definition[(Invitation, BigInt) => Boolean](
    "whether an invitation is open at a moment: it can be accepted then")
  val gone = Definition[(Document, BigInt) => Boolean](
    "whether a document is gone at a moment: past restoring, purged by the next housekeeping")
  val isPending = Definition[(AccessRequest, BigInt) => Boolean](
    "whether an access request is pending at a moment: it can be approved then")
  val reminderDue = Definition[(AccessRequest, BigInt) => Boolean](
    "whether the owner is due a reminder of an access request at a moment")

  // ---------------------------------------------------------------------------
  // the durations
  // ---------------------------------------------------------------------------

  val invitationLasts = Definition[BigInt]("how long an invitation stays open after it is sent, in seconds")
  val trashKeeps = Definition[BigInt]("how long a document stays in the trash before it is gone, in seconds")
  val requestLasts = Definition[BigInt]("how long an access request stays pending after it is made, in seconds")
  val remindAfter = Definition[BigInt](
    "how long after an access request is made its document's owner is reminded of it, in seconds")

  // ---------------------------------------------------------------------------
  // in force, open, gone
  // ---------------------------------------------------------------------------

  val inForceCode = define { (s: Term[Share], t: Term[BigInt]) => s.until.forall(end => t < end) }

  val isOpenCode = define { (i: Term[Invitation], t: Term[BigInt]) => t < i.sent + invitationLasts }

  val goneCode = define { (doc: Term[Document], t: Term[BigInt]) => doc.trashed.exists(at => at + trashKeeps <= t) }

  val isPendingCode = define { (r: Term[AccessRequest], t: Term[BigInt]) => t < r.asked + requestLasts }

  val reminderDueCode = define { (r: Term[AccessRequest], t: Term[BigInt]) => r.asked + remindAfter <= t }
