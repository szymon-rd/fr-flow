package sharing.housekeeping

import frflow.*
import sharing.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.notifications.Notifications
import sharing.requests.AccessRequests
import sharing.store.LibraryStore.store
import sharing.time.ClockKept.clock
import sharing.time.Lifetimes.{gone, inForce, isOpen}

/** Housekeeping: the job that tidies the library. Access never waits for it (the meaning reads the clock); it removes
  * what has ended, so the library does not grow with it, and purges the documents gone from the trash.
  */
object Housekeeping:
  val tidy = Definition[(Library, BigInt) => Library]("the library tidied at a moment")
  val housekeep = Definition[Program[Unit]]("a run of housekeeping on the store, at the time the clock gives")

  /** Whether a share is of a document gone at a moment. */
  val ofGone = define { (lib: Term[Library], t: Term[BigInt], s: Term[Share]) =>
    lib.documents.exists(doc => gone(doc, t) && s.what === make[Target.Doc](doc.id)) }

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

  /** One run, one transaction: the time, the library, the library housekeeping leaves saved when it changed. */
  final class HousekeepingRun[F[_]](store: sharing.store.LibraryStore[F, Term], clock: Clock[F, Term])(
      using f: Flow[F]):
    def run: F[Term[Unit]] = f.atomically(f.flatMap(clock.now)(t => f.flatMap(store.load) { lib =>
      val next = Notifications.warn(AccessRequests.chase(Audit.forget(tidy(lib, t), t), t), t)
      f.as(f.cond(next =!= lib)(store.save(Audit.record(next, t, Change.Housekept)), f.unit), (): Term[Unit]) }))

  val housekeeping = program { HousekeepingRun(store.recording, clock.recording).run }
