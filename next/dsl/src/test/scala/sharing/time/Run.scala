package sharing.time

import examples.Folds.*
import frflow.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.invitations.Invitations
import sharing.notifications.Notifications
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.trash.Trash

/** The service over time: where it is at one moment of its run. `tidied`: when housekeeping last ran. `mailbox`: the
  * notices the mail server has delivered, oldest first.
  */
final case class Moment(library: Library, now: BigInt, tidied: BigInt, mailbox: List[Notice]) derives LeanType

/** What happens to the service: a request answered, a run of housekeeping, a notice of a person delivered, or time
  * passing (in seconds). A request or a run that fails changes nothing: it is no event of the run.
  */
enum Event derives LeanType:
  case Asked(request: Request)
  case Housekept
  case Delivered(to: PersonId)
  case Waited(seconds: BigInt)

/** The service as a transition system: each event moves it from one moment to the next; a run is the events so far,
  * from the start. Claims of every moment the service reaches are stated of `after(events)`.
  */
object Run:
  val startedAt = Definition[BigInt]("when the service started, in seconds")
  val events = Definition[List[Event]]("what has happened to the service since it started, in order: the requests " +
    "answered, the runs of housekeeping, and time passing")
  val housekeepingWithin = Definition[BigInt]("the longest the service goes without a run of housekeeping, in seconds")

  /** The library a request leads to, by the operations' proven code. */
  val answered = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((_, _) => lib)
      .on[Request.Share]((by, what, withWhom, level, until) =>
        Sharing.shareCode(lib, t, by, make[Share](what, withWhom, level, until)))
      .on[Request.Unshare]((by, what, withWhom) => Sharing.unshareCode(lib, t, by, what, withWhom))
      .on[Request.Move]((by, d, into) => Sharing.moveCode(lib, t, by, d, into))
      .on[Request.Invite]((by, to, what, level) => Invitations.inviteCode(lib, t, by, to, what, level))
      .on[Request.Accept]((p, what) => Invitations.acceptCode(lib, t, p, what))
      .on[Request.Withdraw]((by, to, what) => Invitations.withdrawCode(lib, t, by, to, what))
      .on[Request.Trash]((by, d) => Trash.trashCode(lib, t, by, d))
      .on[Request.Restore]((by, d) => Trash.restoreCode(lib, t, by, d))
      .on[Request.Ask]((p, d, level) => AccessRequests.askCode(lib, t, p, d, level))
      .on[Request.Approve]((by, p, d) => AccessRequests.approveCode(lib, t, by, p, d))
      .on[Request.Decline]((by, p, d) => AccessRequests.declineCode(lib, t, by, p, d))
      .on[Request.Transfer]((by, d, to) => Ownership.transferCode(lib, t, by, d, to)) }

  /** The library a request leaves by the proven code: when it changes the library, the change, recorded in the log
    * and announced in the outbox.
    */
  val servedByCode = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    let(answered(lib, t, r))(next => when(next =!= lib)(Notifications.announceCode(
      Audit.recordCode(next, t, make[Change.Made](r)), lib, r, make[Entry](next.log.length, t, make[Change.Made](r))))
      .otherwise(lib)) }

  /** The library a run of housekeeping leaves at a moment: tidied and the requests chased; when that changes it,
    * recorded in the log.
    */
  val housekept = define { (lib: Term[Library], t: Term[BigInt]) =>
    let(Notifications.warnCode(AccessRequests.chaseCode(Audit.forgetCode(Housekeeping.tidyCode(lib, t), t), t), t))(
      next => when(next =!= lib)(Audit.recordCode(next, t, Change.Housekept)).otherwise(lib)) }

  /** The next moment: a request changes the library as it is served at this moment, a run of housekeeping tidies it, a
    * delivery moves the oldest notice of a person in the outbox to the mail server (which keeps it once), and waiting
    * moves the time on.
    */
  val step = define { (m: Term[Moment], e: Term[Event]) =>
    e.on[Event.Asked](r => m.updated(_.library, servedByCode(m.library, m.now, r)))
      .on(Event.Housekept)(m.updated(_.library, housekept(m.library, m.now)).updated(_.tidied, m.now))
      .on[Event.Delivered](p => m.library.outbox.firstWhere(x => x.to === p).fold(m)(n =>
        m.updated(_.library, m.library.updated(_.outbox, m.library.outbox.filter(x => x =!= n)))
          .updated(_.mailbox, when(m.mailbox.contains(n))(m.mailbox).otherwise(m.mailbox :+ n))))
      .on[Event.Waited](d => m.updated(_.now, m.now + d)) }

  /** Where the service is after some events: from an empty library, at the time it started. */
  val after = define { (es: Term[List[Event]]) =>
    es.foldLeft(make[Moment](Library(Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil): Term[Library], startedAt, startedAt,
      Nil: Term[List[Notice]]))((m, e) => step(m, e)) }

  val housekeepingPeriod = Node.claim("Housekeeping is started every minute; the service never goes more than two " +
      "minutes without a run.")(housekeepingWithin === 120)

  val clockNeverGoesBack = Node.assumption("Time never goes back between the service's events: each wait is of no " +
      "time or more.")(
    forall((pre: Term[List[Event]], e: Term[Event], post: Term[List[Event]]) => (events === pre ++ (e :: post)) implies
      e.on[Event.Asked](_ => True).on(Event.Housekept)(True).on[Event.Delivered](_ => True)
        .on[Event.Waited](d => d >= 0)))

  val housekeepingOnTime = Node.assumption("Housekeeping runs often enough: time never moves on more than two " +
      "minutes past its last run.")(
    forall((pre: Term[List[Event]], e: Term[Event], post: Term[List[Event]]) => (events === pre ++ (e :: post)) implies
      e.on[Event.Asked](_ => True).on(Event.Housekept)(True).on[Event.Delivered](_ => True)
        .on[Event.Waited](d => after(pre).now + d <= after(pre).tidied + housekeepingWithin)))
