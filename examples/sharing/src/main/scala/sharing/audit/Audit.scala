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
        .on[Request.Approve]((_, p, d) => s.what === Target[Target.Doc](d) && s.withWhom === Grantee[Grantee.Person](p) && s.until.isEmpty)
        .on[Request.Decline]((_, _, _) => False)
        .on[Request.Transfer]((_, d, to) => s === Share(Target[Target.Doc](d), Grantee[Grantee.Person](to), Level.Edit, none[BigInt])))
      .on[Change.Housekept.type](False)
  }

  /** The branch: what the log is for. Its part is recording; that each change is recorded is the service's run. */
  val auditTrail = Node.claim("AuditTrail",
    "Every change the service makes is recorded in its log, with the request that made it and when, in the same save as the change; so at every moment, every share the library holds was made by a request in the log. A share is never seen before its entry is there, and every yes of canView rests on shares whose making is logged.",
    why = "Q15: every change is logged with who, what and when, and every yes of canView is traceable to the log entries of the shares that gave it. Recording the change in the save that makes it is what puts the entry there first (an ordering of the run, assertion 5 of the time design): no moment of the service shows a share whose entry is not already kept. That the log is append-only and kept for a year is the store's (LibraryKept): nothing removes an entry.",
    idea = "Audit"
  )(after(events).library.shares.forall(s => after(events).library.log.exists(e => makes(e, s))) &&
    forall((p: Term[PersonId], d: Term[DocumentId]) =>
      mayView(after(events).library, after(events).now, p, Target[Target.Doc](d)) ==>
        after(events).library.shares.exists(s => inForce(s, after(events).now) && reaches(after(events).library, s, p) &&
          covers(after(events).library, s, Target[Target.Doc](d)) && after(events).library.log.exists(e => makes(e, s)))))
    .under(accessFollowsShares)

  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val shared = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)

  val recordContract = Node.contract(record)("RecordContract",
    "Recording a change at a moment adds one entry at the end of the log: numbered by its place in it, with the moment and the change. Nothing else changes, and no entry is taken away.",
    why = "Q15: the log is append-only; an entry's number is its place, so entries are never renumbered, and a notice can name the entry it is about.",
    idea = "Audit"
  )((lib, t, c, result) => result === lib.copy((log = lib.log ++ List(Entry(lib.log.length, t, c)))))
    .under(auditTrail, sharing.notifications.Notifications.noticesFollowChanges, sharing.time.Deadlines.invitationsLapseOnTime,
      sharing.time.Deadlines.trashPurgedOnTime, sharing.time.Deadlines.requestsAnsweredOnTime)
    .examples()(
      expect(library, now, Change.Made(shared), library.copy(log = List(Entry(0, now, Change.Made(shared)))), "the first entry is number 0"),
      expect(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept,
        library.copy(log = List(Entry(0, now, Change.Made(shared)), Entry(1, now + 60, Change.Housekept))), "the next is number 1"),
      reject(library.copy(log = List(Entry(0, now, Change.Made(shared)))), now + 60, Change.Housekept,
        library.copy(log = List(Entry(1, now + 60, Change.Housekept))), "an entry is never taken away"))

  val recordCode = define { (lib: Term[Library], t: Term[BigInt], c: Term[Change]) =>
    lib.copy((log = lib.log ++ List(Entry(lib.log.length, t, c))))
  }
