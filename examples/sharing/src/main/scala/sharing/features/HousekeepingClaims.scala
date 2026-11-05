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
  val tidyContract = Node.claim("Tidying at a moment keeps the shares in force, except those of a document gone; " +
      "keeps the invitations still open; and keeps the documents not gone. Everything else stays as it was.")(
    forall((lib: Term[Library], t: Term[BigInt]) => tidy(lib, t) === lib
      .updated(_.documents, lib.documents.filter(doc => !gone(doc, t)))
      .updated(_.shares, lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)))
      .updated(_.invitations, lib.invitations.filter(i => isOpen(i, t)))))
    .refines(housekeepingClearsOnlyTheEnded)

  val housekeepingJob = Node.claim("A run of housekeeping leaves the store holding the library it held, tidied, its " +
      "old log entries forgotten, its access requests chased and the shares ending in a day told of, at the time the " +
      "clock gives, and, when that changed it, recorded in the log; and keeps that time as when it last ran. A run " +
      "that fails changes nothing, and the next minute's run tries again.")(
    housekeep.result.fold(_ => housekeep.changesNothing, _ =>
      val after = housekeep.after
      libraryModel.in(after) === housekeptAt(libraryModel.current, clockModel.current) &&
        housekeptModel.in(after) === clockModel.current && mailerModel.in(after) === mailerModel.current))
    .assuming(oneTransactionAtATime, housekeptOneAtATime, housekeepingOnTime)
