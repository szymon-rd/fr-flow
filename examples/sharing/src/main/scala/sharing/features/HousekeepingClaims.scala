package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Housekeeping.*
import sharing.notifications.Notifications.mailerModel
import sharing.store.LibraryStore.{libraryModel, oneTransactionAtATime}
import sharing.time.ClockKept.{clockModel, housekeepingOnTime, housekeptModel, housekeptOneAtATime}
import sharing.time.Lifetimes.{gone, inForce, isOpen}

/** Housekeeping's claims: what its code is proven to do, each refining a branch or the purpose. */
object HousekeepingClaims:
  val tidyContract = Node.claim("Tidying at a moment keeps only the shares in force and not of a document gone, the " +
      "invitations still open, and the documents not gone.")(
    forall((lib: Term[Library], t: Term[BigInt]) => tidy(lib, t) === lib
      .updated(_.documents, lib.documents.filter(doc => !gone(doc, t)))
      .updated(_.shares, lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)))
      .updated(_.invitations, lib.invitations.filter(i => isOpen(i, t)))))
    .refines(housekeepingClearsOnlyTheEnded)

  /** A root of its own: what a run of housekeeping does to the library. */
  val housekeepingJob = Node.claim("A run of housekeeping leaves the store holding the library it held, housekept " +
      "at the time the clock gives.")(
    housekeep.result.fold(_ => True, _ =>
      libraryModel.in(housekeep.after) === housekeptAt(libraryModel.current, clockModel.current)))
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)

  /** A root of its own: what else a run of housekeeping does, and what a run the store fails does. Apart from
    * housekeepingJob, so that the examples of what housekeeping calls are read beside one claim about its runs.
    */
  val housekeepingRunsCleanly = Node.claim("A run of housekeeping notes the time it ran and sends no mail itself, " +
      "and changes nothing when the store fails it.")(
    housekeep.result.fold(_ => housekeep.changesNothing, _ =>
      housekeptModel.in(housekeep.after) === clockModel.current &&
        mailerModel.in(housekeep.after) === mailerModel.current))
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)

  val failedHousekeepingChangesNothing = Node.claim("A run of housekeeping the store fails changes nothing.")(
    housekeep.result.fold(_ => housekeep.changesNothing, _ => True))
    .refines(housekeepingRunsCleanly)
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)

  val housekeepingNotesItsRun = Node.claim("A run of housekeeping keeps the time the clock gave as when it last ran.")(
    housekeep.result.fold(_ => True, _ => housekeptModel.in(housekeep.after) === clockModel.current))
    .refines(housekeepingRunsCleanly)
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)

  val housekeepingSendsNoMail = Node.claim("A run of housekeeping sends no mail itself.")(
    housekeep.result.fold(_ => True, _ => mailerModel.in(housekeep.after) === mailerModel.current))
    .refines(housekeepingRunsCleanly)
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)
