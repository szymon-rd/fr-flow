package sharing

import cats.effect.IO
import cats.syntax.all.*
import frflow.*
import frflow.eval.flow.Wall
import sharing.Demo.*
import sharing.domain.*
import sharing.http.SharingHttp
import sharing.housekeeping.Housekeeping
import sharing.notifications.{Mailer, MemoryMailer, MemoryPool, Pool}
import sharing.store.{LibraryStore, MemoryLibraryStore}
import sharing.time.{ClockKept, Housekept}
import scala.concurrent.duration.*
import scala.util.Random

/** Today's scheduler tests, ported on a virtual clock (owner §47: as Cats Effect's `TestControl`): the service's
  * programs run as production runs them (`Running`), time passing between them as the world's own step (`elapse` on
  * the virtual clock), housekeeping started every minute, each wake-up late by up to the delay given. Measured after
  * each step: the deadlines, the schedule (`housekeepingOnTime`: the time never more than two minutes past
  * housekeeping's last run), and that nothing is purged early.
  */
class ScheduleSuite extends munit.CatsEffectSuite:
  // a run kept to the schedule wakes housekeeping each virtual minute over days: thousands of runs
  override val munitIOTimeout = 10.minutes

  /** What a run met, step after step. */
  private final case class Measured(onSchedule: Boolean, trashOnTime: Boolean, invitesOnTime: Boolean,
      requestsOnTime: Boolean)

  /** The service on a virtual clock: `steps` requests and stretches of time (an hour to two days when kept, a day to
    * ten days when not), housekeeping started every minute when `kept`, each wake-up late by up to `late` seconds;
    * not at all when not kept.
    */
  private def run(seed: Long, kept: Boolean, late: Int, steps: Int = 80): IO[Measured] =
    val rnd = Random(seed)
    for
      store <- MemoryLibraryStore.holding(library)
      mail  <- MemoryMailer.holding(Map.empty)
      wall  <- Wall.at(now)
      pool  <- MemoryPool.holding(0)
      ran   <- Housekept.at(now)
      run   <- knowledge.running[IO](LibraryStore.libraryModel := store, Mailer.mailerModel := mail,
                 Clock.clockModel := wall, Pool.poolModel := pool, ClockKept.housekeptModel := ran)
      on     = Passing(run, wall, store, ran)
      seen  <- (1 to steps).toList.foldLeftM(Measured(true, true, true, true)) { (m, _) =>
        stepped(on, kept, late, rnd).flatMap(held =>
          measured(m.copy(onSchedule = m.onSchedule && held), store, wall, ran))
      }
    yield seen

  /** One step: a request drawn and handled (the scheduler waking after it when kept), or time passing. */
  private def stepped(on: Passing, kept: Boolean, late: Int, rnd: Random): IO[Boolean] =
    def pick[A](as: A*): A = as(rnd.nextInt(as.size))
    val (p, t) = (pick(ann, bob, cat), pick(Target.Doc(plan), Target.Doc(q3Report), Target.InFolder(reports)))
    val request: IO[Option[Request]] = rnd.nextInt(7) match
      case 0 => on.wall.time.map(at =>
          Some(Request.Share(ann, t, Grantee.Person(p), Level.View, pick(None, Some(at + day)))))
      case 1 => IO.pure(Some(Request.Invite(ann, p, t, Level.View)))
      case 2 => IO.pure(Some(Request.Accept(p, t)))
      case 3 => IO.pure(Some(Request.Trash(ann, pick(plan, q3Report))))
      case 4 => IO.pure(Some(Request.Restore(ann, pick(plan, q3Report))))
      case 5 => IO.pure(Some(Request.Ask(p, t, Level.View)))
      case _ => IO.pure(None)
    request.flatMap {
      case Some(r) => handled(on.run, r) <* (if kept then due(on) else IO.unit)
      case None    => passing(on, Option.when(kept)(late),
          if kept then pick(day / 24, day / 4, 2 * day) else pick(day, 3 * day, 10 * day), rnd)
    }

  private def handled(run: frflow.eval.Running[IO], r: Request): IO[Boolean] =
    run(SharingHttp.handleRequest)(r).as(true)

  /** What time passing runs on: the service, its clock, its store, and when housekeeping last ran. */
  private final case class Passing(run: frflow.eval.Running[IO], wall: Wall, store: MemoryLibraryStore, ran: Housekept)

  /** Time passing, a minute at a time: housekeeping started each minute (a wake-up late by up to `late` seconds), or
    * never; whether the schedule held at each wake-up. Housekeeping purging what has not ended is caught at once.
    */
  private def passing(on: Passing, late: Option[Int], seconds: BigInt, rnd: Random): IO[Boolean] = late match
    case None    => on.wall.elapse(seconds).as(true)
    case Some(l) =>
      val delay = BigInt(if l == 0 then 0 else rnd.nextInt(l + 1))
      if seconds <= 0 then IO.pure(true)
      else
        val step = (BigInt(60) + delay).min(seconds)
        for
          _    <- on.wall.elapse(step)
          held <- (on.wall.time, on.ran.last).mapN((t, last) => t <= last + 120)
          _    <- housekept(on.run, on.wall, on.store)
          rest <- passing(on, late, seconds - step, rnd)
        yield held && rest

  /** The scheduler's wake-up while requests are handled (each may take the time a race with its limit takes): a run
    * of housekeeping once a minute has passed since the last.
    */
  private def due(on: Passing): IO[Unit] =
    (on.wall.time, on.ran.last).flatMapN((t, last) =>
      if t - last >= 60 then housekept(on.run, on.wall, on.store) else IO.unit)

  /** A run of housekeeping; what it purges must have been gone already. */
  private def housekept(run: frflow.eval.Running[IO], wall: Wall, store: MemoryLibraryStore): IO[Unit] =
    for
      before <- store.library
      _      <- run(Housekeeping.housekeeping).void
      after  <- store.library
      at     <- wall.time
    yield assert(before.documents.filterNot(after.documents.contains).forall(_.trashed.exists(_ + 30 * day <= at)),
      "housekeeping purged a document not gone")

  private def measured(m: Measured, store: MemoryLibraryStore, wall: Wall, ran: Housekept): IO[Measured] =
    (store.library, wall.time, ran.last).mapN { (lib, t, last) =>
      Measured(m.onSchedule && t <= last + 120,
        m.trashOnTime && lib.documents.forall(_.trashed.forall(at => t < at + 30 * day + 120)),
        m.invitesOnTime && lib.invitations.forall(i => t < i.sent + 7 * day + 120),
        m.requestsOnTime && lib.requests.forall(r => t < r.asked + 7 * day + 120 &&
          (r.reminded || t < r.asked + 2 * day + 120)))
    }

  test("runs that keep to the schedule meet every deadline; without housekeeping the deadlines fail; nothing is " +
      "purged early either way") {
    for
      kept   <- (1 to 2).toList.traverse(s => run(s, kept = true, late = 60))
      broken <- (1 to 12).toList.traverse(s => run(100 + s, kept = false, late = 0, steps = 200))
    yield
      assert(kept.forall(_ == Measured(true, true, true, true)), kept)
      assert(broken.exists(!_.onSchedule) && broken.exists(!_.trashOnTime) && broken.exists(!_.invitesOnTime),
        broken)
  }

  test("late wake-ups: housekeeping started each minute, a wake-up a minute or more late breaks the schedule, " +
      "which the deadlines rest on; on time, it holds") {
    for
      onTime <- (1 to 1).toList.traverse(s => run(200 + s, kept = true, late = 60))
      late   <- (1 to 2).toList.traverse(s => run(300 + s, kept = true, late = 600))
    yield
      assert(onTime.forall(_.onSchedule), onTime)
      assert(late.exists(!_.onSchedule), late)
  }
