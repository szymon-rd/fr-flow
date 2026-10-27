package sharing.housekeeping

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.notifications.Notifications
import sharing.notifications.Notifications.mailerModel
import sharing.requests.AccessRequests
import sharing.store.LibraryStore.{libraryKept, libraryModel, oneTransactionAtATime, store}
import sharing.time.ClockKept.{clock, clockAlone, clockKept, clockModel}
import sharing.time.Lifetimes.{gone, inForce, isOpen}

/** Housekeeping: the job that tidies the library. Access never waits for it (the meaning reads the clock); it removes
  * what has ended, so the library does not grow with it, and purges the documents gone from the trash.
  */
object Housekeeping:
  val tidy = Definition[(Library, BigInt) => Library]("the library tidied at a moment")
  val housekeep = Definition[Program[Unit]]("a run of housekeeping on the store, at the time the clock gives")

  /** The branch: what housekeeping may do. */
  val housekeepingClearsOnlyTheEnded = Node.claim("Housekeeping clears away only what has ended: shares no longer in " +
      "force or of a document gone, invitations no longer open, and documents gone; and what has ended stays ended, " +
      "so nothing it clears could have counted again.")(
    forall((lib: Term[Library], t: Term[BigInt]) =>
      lib.shares.forall(s => tidy(lib, t).shares.contains(s) || !inForce(s, t) ||
        lib.documents.exists(doc => gone(doc, t) && s.what === make[Target.Doc](doc.id))) &&
      lib.invitations.forall(i => tidy(lib, t).invitations.contains(i) || !isOpen(i, t)) &&
      lib.documents.forall(doc => tidy(lib, t).documents.contains(doc) || gone(doc, t))) &&
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) implies
      (forall((s: Term[Share]) => !inForce(s, t) implies !inForce(s, u)) &&
        forall((i: Term[Invitation]) => !isOpen(i, t) implies !isOpen(i, u)) &&
        forall((doc: Term[Document]) => gone(doc, t) implies gone(doc, u)))))
    .refines(accessFollowsShares)

  /** Whether a share is of a document gone at a moment. */
  val ofGone = define { (lib: Term[Library], t: Term[BigInt], s: Term[Share]) =>
    lib.documents.exists(doc => gone(doc, t) && s.what === make[Target.Doc](doc.id)) }

  val tidyContract = Node.claim("Tidying at a moment keeps the shares in force, except those of a document gone; " +
      "keeps the invitations still open; and keeps the documents not gone. Everything else stays as it was.")(
    forall((lib: Term[Library], t: Term[BigInt]) => tidy(lib, t) === lib
      .updated(_.documents, lib.documents.filter(doc => !gone(doc, t)))
      .updated(_.shares, lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)))
      .updated(_.invitations, lib.invitations.filter(i => isOpen(i, t)))))
    .refines(housekeepingClearsOnlyTheEnded)

  val tidyCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.documents, lib.documents.filter(doc => !gone(doc, t)))
      .updated(_.shares, lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)))
      .updated(_.invitations, lib.invitations.filter(i => isOpen(i, t))) }

  /** What a run leaves at a moment: tidied, its old entries forgotten, its requests chased, the ending shares told of;
    * when that changed it, recorded in the log.
    */
  val housekeptAt = define { (lib: Term[Library], t: Term[BigInt]) =>
    let(Notifications.warn(AccessRequests.chase(Audit.forget(tidy(lib, t), t), t), t))(next =>
      when(next =!= lib)(Audit.record(next, t, Change.Housekept)).otherwise(lib)) }

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

  /** One run, one transaction: the time, the library, the library housekeeping leaves saved when it changed. */
  final class HousekeepingRun[F[_]](store: sharing.store.LibraryStore[F, Term], clock: Clock[F, Term])(
      using f: Flow[F]):
    def run: F[Term[Unit]] = f.atomically(f.flatMap(clock.now)(t => f.flatMap(store.load) { lib =>
      val next = Notifications.warn(AccessRequests.chase(Audit.forget(tidy(lib, t), t), t), t)
      f.as(f.cond(next =!= lib)(store.save(Audit.record(next, t, Change.Housekept)), f.unit), (): Term[Unit]) }))

  val housekeeping = program { HousekeepingRun(store.recording, clock.recording).run }
