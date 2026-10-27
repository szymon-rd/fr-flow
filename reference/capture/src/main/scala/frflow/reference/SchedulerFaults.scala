package frflow.reference

import cats.effect.SyncIO
import frflow.*
import scala.util.Random
import _root_.sharing.Demo.*
import _root_.sharing.domain.*
import _root_.sharing.housekeeping.Housekeeping
import _root_.sharing.http.StoreHttp
import _root_.sharing.service.SharingService
import _root_.sharing.store.MemoryLibraryStore

/** sharing's two scheduler faults, as `SharingSuite` seeds them: housekeeping not run (seeds 101 to 120), and late
  * wake-ups of the scheduler (`Random(7)`). `run` and `gaps` are copies of the suite's, `var`s and all.
  */
object SchedulerFaults:
  final case class Measured(neverEarly: Boolean, trashOnTime: Boolean, invitesOnTime: Boolean,
      endedGiveNothing: Boolean)

  def all: List[Seeded] = List(notRun, lateWakeUps)

  private def notRun: Seeded =
    val lines = (1 to 20).map(s => s"  seed $s, kept: ${run(s, kept = true)}") ++
      (1 to 20).map(s => s"  seed ${100 + s}, not run: ${run(100 + s, kept = false)}")
    Seeded("housekeeping not run", inTable = false,
      "200 generated requests and waits on the fake clock; housekeeping within every 6 hours (kept), or never " +
        "(not run)",
      "SharingSuite: runs that keep to the scheduler's assumption meet every deadline; never-before and ended shares " +
        "hold in every run (not run: a deadline fails in some run, the meaning holds in all)",
      "what each run measured (Measured(neverEarly, trashOnTime, invitesOnTime, endedGiveNothing)):" :: lines.toList)

  private def lateWakeUps: Seeded =
    val rnd = Random(7)
    val lines = (1 to 50).toList.map { i =>
      val delays = List.fill(10)(BigInt(rnd.between(0, 120)))
      val g = gaps(delays)
      s"  round $i: delays ${delays.mkString(" ")}; gaps ${g.mkString(" ")}; HousekeepingOnTime " +
        (if g.forall(_ <= 120) then "holds" else "broken")
    }
    Seeded("late wake-ups of the scheduler", inTable = false,
      "Housekeeping.schedule on a fake clock that wakes it 0 to 119 seconds late, 10 times a round, 50 rounds",
      "SharingSuite: the scheduler on a fake clock with adversarial delays: late wake-ups break HousekeepingOnTime",
      "the gaps between runs (each delay plus the 60 s period); HousekeepingOnTime holds when none is over 120:" ::
        lines)

  private def gaps(delays: List[BigInt]): List[BigInt] =
    val clock = FakeClock(now)
    clock.delay(delays*)
    val starts = List.newBuilder[BigInt]
    Housekeeping.schedule.schedule[SyncIO](clock, times = Some(delays.size + 1), started = starts += _)(() =>
      SyncIO.unit).unsafeRunSync()
    val s = starts.result()
    s.zip(s.tail).map((a, b) => b - a)

  private def run(seed: Long, kept: Boolean, period: BigInt = 6 * 3600): Measured =
    val rnd = Random(seed)
    def pick[A](as: A*): A = as(rnd.nextInt(as.size))
    val clock = FakeClock(now)
    val store = MemoryLibraryStore(library)
    val service = StoreHttp(store, clock)
    var tidied = clock.time
    var m = Measured(true, true, true, true)
    def housekeep(): Unit =
      val before = store.library
      service.housekeep()
      tidied = clock.time
      val removed = before.documents.filterNot(store.library.documents.contains)
      if !removed.forall(_.trashed.exists(_ + 30 * day <= clock.time)) then m = m.copy(neverEarly = false)
    def measure(): Unit =
      val (lib, t) = (store.library, clock.time)
      if !lib.documents.forall(_.trashed.forall(at => t < at + 30 * day + period)) then m = m.copy(trashOnTime = false)
      if !lib.invitations.forall(i => t < i.sent + 7 * day + period) then m = m.copy(invitesOnTime = false)
      val ended = lib.copy(shares = lib.shares.filter(_.until.forall(t < _)))
      for p <- List(ann, bob, cat); d <- List(plan, q3Report) do
        if SharingService.access(lib, t, p, d) != SharingService.access(ended, t, p, d) then
          m = m.copy(endedGiveNothing = false)
    for _ <- 1 to 200 do
      val p = pick(ann, bob, cat)
      val t = pick(Target.Doc(plan), Target.Doc(q3Report), Target.InFolder(reports))
      rnd.nextInt(6) match
        case 0 =>
          service.handle(Request.Share(ann, t, Grantee.Person(p), Level.View, pick(None, Some(clock.time + day))))
        case 1 => service.handle(Request.Invite(ann, p, t, Level.View))
        case 2 => service.handle(Request.Accept(p, t))
        case 3 => service.handle(Request.Trash(ann, pick(plan, q3Report)))
        case 4 => service.handle(Request.Restore(ann, pick(plan, q3Report)))
        case _ =>
          var left = pick(day, 3 * day, 10 * day)
          while left > 0 do
            val d = if kept then left.min(tidied + period - clock.time) else left
            clock.advance(d); left -= d
            if kept then housekeep()
      measure()
    if !kept then housekeep()
    m
