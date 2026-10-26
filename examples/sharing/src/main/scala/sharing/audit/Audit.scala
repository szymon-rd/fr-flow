package sharing.audit

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.inForce
import sharing.time.Run.{after, events}

/** The log: every change the service makes, recorded with the request that made it (who asked, what) and when, in
  * the same save as the change. A function of the library and of the moment.
  */
trait Audit:
  /** The library with `change`, made at `now`, recorded in its log. */
  def record(library: Library, now: BigInt, change: Change): Library

/** The log's contract, its code, and the branch it is part of. */
object Audit:
  import Demo.*

  val record = Param[(Library, BigInt, Change) => Library]("record", "the library with a change recorded in its log")

  /** Whether a log entry is of the request that made a share: the share asked for, an accepted invitation, an approved
    * access request, or a document handed on (the new owner's share).
    */
  val makes = define { (e: Term[Entry], s: Term[Share]) =>
    e.change
      .on[Change.Made](r => r
        .on[Request.Access]((_, _) => False)
        .on[Request.Share]((_, what, withWhom, level, until) => s === Share(what, withWhom, level, until))
        .on[Request.Unshare]((_, _, _) => False)
        .on[Request.Move]((_, _, _) => False)
        .on[Request.Invite]((_, _, _, _) => False)
        .on[Request.Accept]((p, what) => s.what === what && s.withWhom === Grantee[Grantee.Person](p) && s.until.isEmpty)
        .on[Request.Withdraw]((_, _, _) => False)
        .on[Request.Trash]((_, _) => False)
        .on[Request.Restore]((_, _) => False)
        .on[Request.Ask]((_, _, _) => False)
        .on[Request.Approve]((_, p, w) => s.what === w && s.withWhom === Grantee[Grantee.Person](p) && s.until.isEmpty)
        .on[Request.Decline]((_, _, _) => False)
        .on[Request.Transfer]((_, d, to) => s === Share(Target[Target.Doc](d), Grantee[Grantee.Person](to), Level.Edit, none[BigInt])))
      .on[Change.Housekept.type](False)
      .on[Change.Forgotten.type](False)
  }

  /** The branch: what the log is for. Its part is recording; that each change is recorded is the service's run. */
  val auditTrail = Node.claim("AuditTrail",
    "Every change the service makes is recorded in its log, with the request that made it and when, in the same save as the change; so at every moment, every share the library holds was made by a request in the log. A share is never seen before its entry is there, and every yes of canView rests on shares whose making is logged.",
    why = "Q15: every change is logged with who, what and when, and every yes of canView is traceable to the log entries of the shares that gave it. Recording the change in the save that makes it is what puts the entry there first (an ordering of the run, assertion 5 of the time design): no moment of the service shows a share whose entry is not already kept. Nothing removes an entry (LibraryKept); housekeeping forgets what an entry tells after a year, but not while it explains a share held (ForgetContract).",
    idea = "Audit"
  )(after(events).library.shares.forall(s => after(events).library.log.exists(e => makes(e, s))) &&
    forall((p: Term[PersonId], d: Term[DocumentId]) =>
      mayView(after(events).library, after(events).now, p, Target[Target.Doc](d)) implies
        after(events).library.shares.exists(s => inForce(s, after(events).now) && reaches(after(events).library, s, p) &&
          covers(after(events).library, s, Target[Target.Doc](d)) && after(events).library.log.exists(e => makes(e, s)))))
    .refines(accessFollowsShares)

  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val shared = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)

  val recordContract = Node.contract(record)("RecordContract",
    "Recording a change at a moment adds one entry at the end of the log: numbered by its place in it, with the moment and the change. Nothing else changes, and no entry is taken away.",
    why = "Q15: the log is append-only; an entry's number is its place, so entries are never renumbered, and a notice can name the entry it is about.",
    idea = "Audit"
  )((lib, t, c, result) => result === lib.copy((log = lib.log ++ List(Entry(lib.log.length, t, c)))))
    .refines(auditTrail, sharing.notifications.Notifications.noticesFollowChanges, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)
    .examples()(
      expect(library, now, Change.Made(shared), library.copy(log = List(Entry(0, now, Change.Made(shared)))), "the first entry is number 0"),
      expect(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept,
        library.copy(log = List(Entry(0, now, Change.Made(shared)), Entry(1, now + 60, Change.Housekept))), "the next is number 1"),
      never(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept,
        library.copy(log = List(Entry(1, now + 60, Change.Housekept))), "an entry is never taken away"))

  val recordCode = define { (lib: Term[Library], t: Term[BigInt], c: Term[Change]) =>
    lib.copy((log = lib.log ++ List(Entry(lib.log.length, t, c))))
  }

  val forget = Param[(Library, BigInt) => Library]("forget", "the library with the changes of its old log entries forgotten")

  /** A year, in seconds: how long the log keeps what an entry tells. */
  val year: BigInt = 365 * day
  /** Whether an entry still explains something: the making of a share the library holds, or the change a notice
    * waiting in the outbox tells of.
    */
  val explains = define { (lib: Term[Library], e: Term[Entry]) =>
    lib.shares.exists(s => makes(e, s)) || lib.outbox.exists(n => n.about === Subject[Subject.Logged](e))
  }

  private val oldShare = Entry(0, now - 400 * day, Change.Made(shared))
  private val oldUnshare = Entry(1, now - 400 * day, Change.Made(Request.Unshare(ann, Target.Doc(plan), Grantee.Person(bob))))

  val forgetContract = Node.contract(forget)("ForgetContract",
    "Housekeeping forgets, at a moment, the change of each log entry made more than a year before, unless the entry is the making of a share the library holds or of a change a notice waiting in the outbox tells of: the entry stays in its place, with its number and time, and its change is forgotten. Nothing else changes.",
    why = "Q15: the log is kept for a year. An entry keeps its place, so numbers stay unique and no entry is taken away (RecordContract); what it told is gone. An entry that explains a share held, or a notice not yet sent, is kept as long as it does (AuditTrail, NoticesFollowChanges).",
    idea = "Audit"
  )((lib, t, result) => result === lib.copy((log = lib.log.map(e =>
    (e.at <= t - year && !explains(lib, e)).fold(Entry(e.id, e.at, Change.Forgotten: Term[Change]), e)))))
    .refines(auditTrail)
    .examples()(
      expect(library.copy(shares = bobViewsPlan :: library.shares, log = List(oldShare, oldUnshare)), now,
        library.copy(shares = bobViewsPlan :: library.shares, log = List(oldShare, oldUnshare.copy(change = Change.Forgotten))),
        "over a year on: the unshare is forgotten; the share it made, still held, keeps its entry"),
      expect(library.copy(log = List(oldUnshare)), now - 100 * day, library.copy(log = List(oldUnshare)), "under a year: kept"),
      never(library.copy(log = List(oldUnshare)), now, library, "an entry is never taken away"))

  val forgetCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.copy((log = lib.log.map(e => (e.at <= t - year && !explains(lib, e)).fold(Entry(e.id, e.at, Change.Forgotten: Term[Change]), e))))
  }
