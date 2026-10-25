package sharing.housekeeping

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.store.LibraryModel
import sharing.store.LibraryStore.store
import sharing.time.Lifetimes.{gone, inForce, isOpen}

/** Housekeeping: the job that tidies the library. Access never waits for it (the meaning reads the clock); it removes
  * what has ended, so the library does not grow with it, and purges the documents gone from the trash.
  */
trait Housekeeping:
  /** The library tidied at a moment. */
  def tidy(library: Library, now: BigInt): Library

/** Housekeeping's contracts: the tidying, and the job that runs it on the store. */
object Housekeeping:
  import Demo.*

  val tidy = Param[(Library, BigInt) => Library]("tidy", "the library tidied at a moment")

  /** The branch: what housekeeping may do. Its parts are tidying and, below the timed words, that they change one way. */
  val clearsOnlyTheEnded = Node.claim("HousekeepingClearsOnlyTheEnded",
    "Housekeeping clears away only what has ended: shares no longer in force or of a document gone, invitations no longer open, and documents gone; and what has ended stays ended, so nothing it clears could have counted again.",
    why = "Q6-Q8: tidying keeps the library from growing with what gives nothing; it is safe because ending is for good. Whether something has ended is left open here (Lifetimes); that it stays ended rests on the clock never going back (EndedStaysEnded).",
    idea = "Time and housekeeping"
  )(forall((lib: Term[Library], t: Term[BigInt]) =>
    lib.shares.forall(s => tidy(lib, t).shares.contains(s) || !inForce(s, t) ||
      lib.documents.exists(doc => gone(doc, t) && s.what === Target[Target.Doc](doc.id))) &&
    lib.invitations.forall(i => tidy(lib, t).invitations.contains(i) || !isOpen(i, t)) &&
    lib.documents.forall(doc => tidy(lib, t).documents.contains(doc) || gone(doc, t))) &&
    forall((t: Term[BigInt], u: Term[BigInt]) => (t <= u) ==>
      (forall((s: Term[Share]) => !inForce(s, t) ==> !inForce(s, u)) &&
       forall((i: Term[Invitation]) => !isOpen(i, t) ==> !isOpen(i, u)) &&
       forall((doc: Term[Document]) => gone(doc, t) ==> gone(doc, u)))))
    .under(accessFollowsShares)

  /** Whether a share is of a document gone at a moment. */
  val ofGone = define { (lib: Term[Library], t: Term[BigInt], s: Term[Share]) =>
    lib.documents.exists(doc => gone(doc, t) && s.what === Target[Target.Doc](doc.id))
  }

  private val ended = library.copy(shares = bobViewsPlanForAnHour :: library.shares, invitations = List(catInvited),
    documents = List(planTrashed, q3ReportDoc))

  val tidyContract = Node.contract(tidy)("TidyContract",
    "Tidying at a moment keeps the shares in force, except those of a document gone; keeps the invitations still open; and keeps the documents not gone. Everything else stays as it was.",
    why = "Q6–Q8: ended shares and lapsed invitations give nothing and are removed; a document 30 days in the trash is deleted for good, with its shares (Q8), so they cannot come back to anything. The folders and teams are not touched.",
    idea = "Time and housekeeping"
  )((lib, t, result) =>
    result === lib.copy((documents = lib.documents.filterNot(doc => gone(doc, t)),
      shares = lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)),
      invitations = lib.invitations.filter(i => isOpen(i, t)))))
    .under(clearsOnlyTheEnded)
    .examples()(
      expect(ended, now, ended, "nothing has ended yet"),
      expect(ended, now + 3600, ended.copy(shares = library.shares), "Bob's share of the plan has ended"),
      expect(ended, now + 29 * day, library.copy(documents = List(q3ReportDoc), shares = List(annEditsReports, engViewsReports)),
        "a month on: the invitation has lapsed, and the plan is gone with its shares"),
      reject(ended, now, library, "nothing is removed before its time"))

  val tidyCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.copy((documents = lib.documents.filterNot(doc => gone(doc, t)),
      shares = lib.shares.filter(s => inForce(s, t) && !ofGone(lib, t, s)),
      invitations = lib.invitations.filter(i => isOpen(i, t))))
  }

  // ---------------------------------------------------------------------------
  // the job: a run reads the clock and tidies what the store holds
  // ---------------------------------------------------------------------------

  val housekeep = Param[() => Flow[Unit]]("housekeep", "a run of housekeeping on the store, at the time the clock gives")

  val jobContract = Node.contract(housekeep)("HousekeepingJob",
    "A run of housekeeping leaves the store holding the library it held, tidied at the time the clock gives; it does not move the clock.",
    why = "The job is how tidying reaches the store. Proven of its flow from the store's and the clock's models (LibraryKept, ClockKept); how often it runs is the scheduler's (HousekeepingOnTime).",
    idea = "Time and housekeeping"
  )((result, before, after) =>
    after(LibraryModel) === tidy(before(LibraryModel), before(ClockModel).now) && after(ClockModel) === before(ClockModel))
    .under(sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.invitationsLapseOnTime)
    .examples()(
      expect(World(LibraryModel -> ended, ClockModel -> ClockState(now + 3600, Nil)), (),
        World(LibraryModel -> ended.copy(shares = library.shares), ClockModel -> ClockState(now + 3600, Nil)), "an hour on: Bob's share goes"),
      expect(World(LibraryModel -> ended, ClockModel -> ClockState(now, Nil)), (),
        World(LibraryModel -> ended, ClockModel -> ClockState(now, Nil)), "nothing has ended yet"),
      reject(World(LibraryModel -> ended, ClockModel -> ClockState(now + 3600, Nil)), (),
        World(LibraryModel -> ended, ClockModel -> ClockState(now + 3600, Nil)), "a run removes what has ended"))

  /** One run: the time, the library, the library tidied saved. HousekeepingJob is proven of it. */
  def housekeeping: Flow[Unit] =
    for
      t   <- Flow.now
      lib <- store.load
      _   <- store.save(tidy(lib, t))
    yield ()

  /** Housekeeping every minute: the scheduler, run in the server. That runs come at least every two minutes is
    * assumed (HousekeepingOnTime), and checked where it runs.
    */
  val schedule: Every = Flow.every(60)(housekeeping)
