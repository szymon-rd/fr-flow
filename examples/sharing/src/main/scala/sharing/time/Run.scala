package sharing.time

import frflow.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.http.Request
import sharing.invitations.Invitations
import sharing.service.Sharing
import sharing.trash.Trash

/** The service over time: where it is at one moment of its run. `tidied`: when housekeeping last ran. */
final case class Moment(library: Library, now: BigInt, tidied: BigInt)
object Moment extends Data[Moment]

/** What happens to the service: a request answered, a run of housekeeping, or time passing (in seconds). */
enum Event:
  case Asked(request: Request)
  case Housekept
  case Waited(seconds: BigInt)
object Event extends Data[Event]

/** The service as a transition system: each event moves it from one moment to the next; a run is the events so far,
  * from the start. Claims of every moment the service reaches are stated of `after(events)`, and proven by induction
  * over the run (`FrFlow.always_when`): each event keeps them, where the assumptions on the run allow it.
  */
object Run:
  val startedAt = Param[BigInt]("startedAt", "when the service started, in seconds")
  val events = Param[List[Event]]("events", "what has happened to the service since it started, in order: the requests answered, the runs of housekeeping, and time passing")
  val housekeepingWithin = Param[BigInt]("housekeepingWithin", "the longest the service goes without a run of housekeeping, in seconds")

  /** The library a request leads to, by the operations' proven code: what HandleContract's flow leaves in the store. */
  val answered = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((_, _) => lib)
      .on[Request.Share]((by, what, withWhom, level, until) => Sharing.shareCode(lib, t, by, Share(what, withWhom, level, until)))
      .on[Request.Unshare]((by, what, withWhom) => Sharing.unshareCode(lib, t, by, what, withWhom))
      .on[Request.Move]((by, d, into) => Sharing.moveCode(lib, t, by, d, into))
      .on[Request.Invite]((by, to, what, level) => Invitations.inviteCode(lib, t, by, to, what, level))
      .on[Request.Accept]((p, what) => Invitations.acceptCode(lib, t, p, what))
      .on[Request.Withdraw]((by, to, what) => Invitations.withdrawCode(lib, t, by, to, what))
      .on[Request.Trash]((by, d) => Trash.trashCode(lib, t, by, d))
      .on[Request.Restore]((by, d) => Trash.restoreCode(lib, t, by, d))
  }

  /** The next moment: a request changes the library as it is answered at this moment, a run of housekeeping tidies it,
    * and waiting moves the time on.
    */
  val step = define { (m: Term[Moment], e: Term[Event]) =>
    e.on[Event.Asked](r => m.copy((library = answered(m.library, m.now, r))))
      .on[Event.Housekept.type](m.copy((library = Housekeeping.tidyCode(m.library, m.now), tidied = m.now)))
      .on[Event.Waited](d => m.copy((now = m.now + d)))
  }

  /** Where the service is after some events: from an empty library, at the time it started. */
  val after = define { (es: Term[List[Event]]) =>
    es.foldLeft(Moment(Library(Nil, Nil, Nil, Nil, Nil), startedAt, startedAt): Term[Moment])((m, e) => step(m, e))
  }

  val housekeepingPeriod = Node.definition("HousekeepingPeriod",
    "Housekeeping is started every minute; the service never goes more than two minutes without a run.",
    why = "Q9: jobs run every minute. A run may start late (a sleep wakes late, the run takes time), so the bound the deadlines are stated with leaves a minute for that."
  )(housekeepingWithin := (120: Term[BigInt]))

  val clockNeverGoesBack = Node.assumption("ClockNeverGoesBack",
    "Time never goes back between the service's events: each wait is of no time or more.",
    why = "Q9: the server's clock never goes back. A clock set back (by hand, or by a time server) would break this; the server reads the clock once per request, so it would answer as if earlier.",
    idea = "Time and housekeeping"
  )(forall((pre: Term[List[Event]], post: Term[List[Event]]) => forall((e: Term[Event]) =>
    (events === pre ++ (e :: post)) ==>
      e.on[Event.Asked](_ => True).on[Event.Housekept.type](True).on[Event.Waited](d => d >= 0))))
    .under(Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime, Deadlines.endedStaysEnded)

  val housekeepingOnTime = Node.assumption("HousekeepingOnTime",
    "Housekeeping runs often enough: time never moves on more than two minutes past its last run.",
    why = "The scheduler starts housekeeping every minute (Housekeeping.schedule); this is what the deadlines need of it. Not proven: the server checks it as it runs, and the tests show which claims fail without it.",
    idea = "Time and housekeeping"
  )(forall((pre: Term[List[Event]], post: Term[List[Event]]) => forall((e: Term[Event]) =>
    (events === pre ++ (e :: post)) ==>
      e.on[Event.Asked](_ => True).on[Event.Housekept.type](True)
        .on[Event.Waited](d => after(pre).now + d <= after(pre).tidied + housekeepingWithin))))
    .under(Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime)
