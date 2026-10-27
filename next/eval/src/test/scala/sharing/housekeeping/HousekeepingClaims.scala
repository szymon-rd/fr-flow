package sharing.housekeeping

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping.*
import sharing.notifications.Notifications.mailerModel
import sharing.store.LibraryStore.{libraryKept, libraryModel, oneTransactionAtATime}
import sharing.time.ClockKept.{clockAlone, clockKept, clockModel}
import sharing.time.Lifetimes.{gone, inForce, isOpen}

/** Housekeeping's claims: what its code is proven to do, each refining a branch or the purpose. */
object HousekeepingClaims:
  val tidyContract = Node.claim("Tidying at a moment keeps the shares in force, except those of a document gone; " +
      "keeps the invitations still open; and keeps the documents not gone. Everything else stays as it was.")(
    forall((lib: Term[Library], t: Term[BigInt]) => tidy(lib, t) === lib
      .updated(_.documents, lib.documents.filter(doc => !gone(doc, t)))
      .updated(_.shares, lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)))
      .updated(_.invitations, lib.invitations.filter(i => isOpen(i, t)))))
    .refines(housekeepingClearsOnlyTheEnded)

  val housekeepingJob = Node.claim("A run of housekeeping leaves the store holding the library it held, tidied, its " +
      "old log entries forgotten, its access requests chased and the shares ending in a day told of, at the time the " +
      "clock gives, and, when that changed it, recorded in the log; it does not move the clock. A run that fails " +
      "changes nothing, and the next minute's run tries again.")(
    forall((before: Term[World]) => housekeep.from(before) { (_, after) =>
      libraryModel.in(after) === housekeptAt(libraryModel.in(before), clockModel.in(before)) &&
        clockModel.in(after) === clockModel.in(before) && mailerModel.in(after) === mailerModel.in(before) }
      .failsChangingNothing[Failure]))
    .refines(sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.requestsAnsweredOnTime)
    .assuming(libraryKept, oneTransactionAtATime, clockKept, clockAlone)
