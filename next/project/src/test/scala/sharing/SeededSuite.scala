package sharing

import cats.effect.{IO, Ref}
import frflow.*
import frflow.eval.flow.Wall
import frflow.eval.run.{Broken, OnCode}
import frflow.testing.ported.Tested
import sharing.Demo.*
import sharing.domain.*
import sharing.examples.AccessExamples
import sharing.http.SharingHttp
import sharing.housekeeping.Housekeeping
import sharing.notifications.{Mailer, MemoryMailer, MemoryPool, Notifications, Pool}
import sharing.service.Sharing
import sharing.store.{LibraryStore, MemoryLibraryStore}
import scala.concurrent.duration.*

/** Section 9's seeded bugs of sharing, after the port: plain Scala access that forgets the end of shares, found by a
  * generated case of accessContract as today; and the fault sweep, each program's runs on the store and the mail
  * server in memory with each call of theirs failing in turn, as production runs them (`Running`): a run that fails
  * changes nothing, and one that does not does what today's examples say; today's flow examples are run so too.
  * The interleavings are `InterleavingsSuite`'s.
  */
class SeededSuite extends munit.CatsEffectSuite:
  /** Today's seeded access: the shares with the person or a team of theirs, of the document or a folder around it,
    * whenever they end.
    */
  private val forgetful: (Library, BigInt, PersonId, DocumentId) => Option[Level] = (lib, _, p, d) =>
    val trashed = lib.documents.exists(doc => doc.id == d && doc.trashed.isDefined)
    val whom = Grantee.Person(p) :: lib.teams.filter(_.members.contains(p)).map(team => Grantee.Team(team.id))
    val places = Target.Doc(d) :: lib.documents.filter(_.id == d).flatMap(_.folders.map(Target.InFolder(_)))
    val shares = lib.shares.filter(s => whom.contains(s.withWhom) && places.contains(s.what))
    if trashed || shares.isEmpty then None
    else if shares.exists(_.level == Level.Edit) then Some(Level.Edit)
    else Some(Level.View)

  test("access that forgets the end of shares passes some of today's examples; a generated case finds it") {
    val buggy = withCode(FrModel("Sharing")(nodes*)).implementTested(Sharing.access)(_ => forgetful)
    assertEquals(Tested.onCode(AccessExamples(buggy)).count(_ == OnCode.Holds), 7)
    assertEquals(Tested.failure(buggy, "accessContract").broke, Broken.Post)
  }

  test("today's examples of the operations, 99 of them, hold on the code") {
    val verdicts = Examples.written.flatMap(Tested.onCode)
    assertEquals((verdicts.size, verdicts.distinct), (99, List(OnCode.Holds)))
  }

  /** A clock whose waits take a hundredth of their seconds, so a race against one is decided by what runs. */
  private def clock(start: BigInt): IO[Wall] = Ref[IO].of(start).map(t => new Wall:
    def now: IO[BigInt] = t.get
    def sleep(seconds: BigInt): IO[Unit] = IO.sleep((seconds * 10).toLong.millis) *> t.update(_ + seconds)
    def elapse(seconds: BigInt): IO[Unit] = t.update(_ + seconds.max(0))
    def time: IO[BigInt] = t.get)

  /** The service in memory from a library and mailboxes at a time, the store's and the mail server's calls taking the
    * faults given: what a program gives (its error on the left), and the library and mailboxes after.
    */
  private def ran[A](lib: Library, at: BigInt, store: List[Boolean], mail: List[Boolean])(
      f: (frflow.eval.Running[IO]) => IO[A]): IO[(Either[Throwable, A], Library, Map[PersonId, List[Notice]])] =
    timed((lib, at), store, mail)(f).map((out, l, b, _) => (out, l, b))

  /** The same, from mailboxes `boxes`, and the clock after too. */
  private def timed[A](from: (Library, BigInt), store: List[Boolean], mail: List[Boolean],
      boxes: Map[PersonId, List[Notice]] = Map.empty)(f: (frflow.eval.Running[IO]) => IO[A])
      : IO[(Either[Throwable, A], Library, Map[PersonId, List[Notice]], BigInt)] =
    for
      s   <- MemoryLibraryStore.holding(from._1)
      m   <- MemoryMailer.holding(boxes)
      w   <- clock(from._2)
      p   <- MemoryPool.holding(0)
      h   <- sharing.time.Housekept.at(from._2)
      run <- knowledge.running[IO](LibraryStore.libraryModel := s, Mailer.mailerModel := m,
               Clock.clockModel := w, Pool.poolModel := p, sharing.time.ClockKept.housekeptModel := h)
      _   <- s.failing(store) *> m.failing(mail)
      out <- f(run).attempt
      l   <- s.library
      b   <- m.boxes
      n   <- p.count
      t   <- w.time
    yield
      assertEquals(n, BigInt(0), "a connection is left taken")
      (out, l, b, t)

  private val shareWithBob = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)

  test("fault sweep, handle: Ann shares the plan with Bob, done and logged; its read or its save failing, nothing") {
    val handle = (r: Request) => (run: frflow.eval.Running[IO]) => run(SharingHttp.handleRequest)(r)
    for
      ok    <- ran(library, now, Nil, Nil)(handle(shareWithBob))
      read  <- ran(library, now, List(true), Nil)(handle(shareWithBob))
      saved <- ran(library, now, List(false, true), Nil)(handle(shareWithBob))
      ask   <- ran(library, now, List(true), Nil)(handle(Request.Access(bob, q3Report)))
    yield
      assertEquals(ok._1.map(_.map(_.toString)), Right(Some("Done")))
      assertEquals(ok._2.shares, bobViewsPlan :: library.shares)
      assertEquals(ok._2.log.map(_.change), List(Change.Made(shareWithBob)))
      List(read, saved, ask).foreach(r => assert(r._1.isLeft && r._2 == library && r._3.isEmpty, r))
  }

  test("fault sweep, housekeeping: an hour on, Bob's share goes and the run is logged; failing, nothing") {
    val start = library.copy(shares = bobViewsPlanForAnHour :: library.shares)
    val job = (run: frflow.eval.Running[IO]) => run(Housekeeping.housekeeping)
    for
      ok    <- ran(start, now + 3600, Nil, Nil)(job)
      read  <- ran(start, now + 3600, List(true), Nil)(job)
      saved <- ran(start, now + 3600, List(false, true), Nil)(job)
    yield
      assertEquals(ok._2.shares, library.shares)
      assertEquals(ok._2.log.map(_.change), List(Change.Housekept))
      List(read, saved).foreach(r => assert(r._1.isLeft && r._2 == start, r))
  }

  private val catTold = Notice(cat, Subject.Logged(Entry(0, now, Change.Made(Request.Invite(ann, cat,
    Target.Doc(plan), Level.View)))))

  test("fault sweep, delivery: Cat's notice delivered once, tried again while the mail server fails, kept when " +
    "it fails three times; an outbox that cannot be read, nothing") {
    val start = library.copy(outbox = List(catTold))
    val job = (run: frflow.eval.Running[IO]) => run(Notifications.delivery)
    for
      ok     <- ran(start, now, Nil, Nil)(job)
      second <- ran(start, now, Nil, List(true))(job)
      never  <- ran(start, now, Nil, List(true, true, true))(job)
      read   <- ran(start, now, List(true), Nil)(job)
    yield
      List(ok, second).foreach(r => assertEquals((r._2.outbox, r._3), (Nil, Map(cat -> List(catTold)))))
      assertEquals((never._1.isRight, never._2, never._3), (true, start, Map.empty[PersonId, List[Notice]]))
      assert(read._1.isLeft && read._2 == start && read._3.isEmpty, read)
  }

  // Today's flow examples (20, of handle, housekeeping and delivery) are run in production's interpreter: those the
  // sweep above does not run, here.

  test("today's examples of handle: Bob's team views the Q3 report and nothing changes; Bob may not share the plan, " +
    "refused, the store keeps the library; Cat has no access to the plan") {
    val handle = (r: Request) => (run: frflow.eval.Running[IO]) => run(SharingHttp.handleRequest)(r)
    for
      views   <- ran(library, now, Nil, Nil)(handle(Request.Access(bob, q3Report)))
      refused <- ran(library, now, Nil, Nil)(handle(Request.Share(bob, Target.Doc(plan), Grantee.Person(bob),
                   Level.Edit, None)))
      cat     <- ran(library, now, Nil, Nil)(handle(Request.Access(sharing.Demo.cat, plan)))
    yield
      assertEquals(views._1.map(_.map(_.toString)), Right(Some("Access(Some(View))")))
      assertEquals(refused._1.map(_.map(_.toString)), Right(Some("Refused")))
      assertEquals(cat._1.map(_.map(_.toString)), Right(Some("Access(None)")))
      List(views, refused, cat).foreach(r => assertEquals(r._2, library))
  }

  test("today's example of housekeeping: nothing has ended yet, nothing to log") {
    val start = library.copy(shares = bobViewsPlanForAnHour :: library.shares)
    ran(start, now, Nil, Nil)(run => run(Housekeeping.housekeeping)).map(r => assertEquals((r._1.isRight, r._2),
      (true, start)))
  }

  private val bobTold = Notice(bob, Subject.Logged(Entry(1, now, Change.Made(Request.Approve(ann, bob,
    Target.Doc(plan))))))
  private val catAgain = Notice(cat, Subject.Logged(Entry(2, now, Change.Made(Request.Share(ann, Target.Doc(plan),
    Grantee.Person(cat), Level.View, None)))))

  test("today's examples of delivery: Cat's first and Bob's go at once, Cat's second waits; down once, delivered a " +
    "second later; down three times, three seconds on; delivered but the store failed, the notice stays; sent " +
    "again after that, not delivered twice") {
    val job = (run: frflow.eval.Running[IO]) => run(Notifications.delivery)
    val one = library.copy(outbox = List(catTold))
    for
      both    <- timed((library.copy(outbox = List(catTold, bobTold, catAgain)), now), Nil, Nil)(job)
      once    <- timed((one, now), Nil, List(true))(job)
      thrice  <- timed((one, now), Nil, List(true, true, true))(job)
      stays   <- timed((one, now), List(false, false, true), Nil)(job)
      again   <- timed((one, now), Nil, Nil, Map(cat -> List(catTold)))(job)
    yield
      assertEquals((both._2.outbox, both._3), (List(catAgain), Map(cat -> List(catTold), bob -> List(bobTold))))
      assertEquals((once._2.outbox, once._3, once._4), (Nil, Map(cat -> List(catTold)), now + 1))
      assertEquals((thrice._2.outbox, thrice._3, thrice._4), (List(catTold), Map.empty[PersonId, List[Notice]],
        now + 3))
      assertEquals((stays._1.isRight, stays._2.outbox, stays._3), (true, List(catTold), Map(cat -> List(catTold))))
      assertEquals((again._2.outbox, again._3), (Nil, Map(cat -> List(catTold))))
  }
