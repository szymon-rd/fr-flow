package sharing

import cats.effect.{IO, Ref}
import cats.effect.std.{Mutex, Random}
import cats.syntax.all.*
import frflow.*
import frflow.core.code.Values
import frflow.core.name.{ModelName, SymbolName}
import frflow.dsl.flow.ReadRecording
import frflow.eval.{Env, Fn, Races, ScalaValue, Semantics}
import frflow.eval.flow.{FlowInterpreter, World}
import frflow.project.Projects
import frflow.testing.Interleavings
import sharing.Demo.*
import sharing.domain.*
import sharing.notifications.{Delivery, Mailer, Pool}
import sharing.store.LibraryStore
import scala.concurrent.duration.*

/** Section 9's interleavings of sharing, over the recorded program: delivery's sends, its branches at once, each call
  * of the models after a random pause, `Interleavings.Runs` times from each start, as today's examples of the job
  * were run; the outbox and the mailboxes every interleaving leaves are the one order's. And a whole run of delivery
  * whose time limit passes before its sends end (a send slower than the limit): its sends cut off part way, every
  * run leaves what the reading Lean proves allows (the loser cut off between two of its steps, `Prog.Cut`), some of
  * them a delivery half done, and a send begun finishes, as a call is never cancelled part way.
  */
class InterleavingsSuite extends munit.CatsEffectSuite:
  private val elaborated = Projects.elaborated(knowledge)
  private val semantics = Semantics(elaborated)

  private val catTold = Notice(cat, Subject.Logged(Entry(0, now, Change.Made(Request.Invite(ann, cat,
    Target.Doc(plan), Level.View)))))
  private val bobTold = Notice(bob, Subject.Logged(Entry(1, now, Change.Made(Request.Approve(ann, bob,
    Target.Doc(plan))))))
  private val catAgain = Notice(cat, Subject.Logged(Entry(2, now, Change.Made(Request.Share(ann, Target.Doc(plan),
    Grantee.Person(cat), Level.View, None)))))

  /** The outbox and the mailboxes each run leaves, from a library whose outbox holds `outbox`. */
  private def interleaved(outbox: List[Notice]): IO[List[(List[Notice], Map[PersonId, List[Notice]])]] =
    for
      seen   <- Ref[IO].of(List.empty[Ref[IO, Map[ModelName, ScalaValue]]])
      worlds  = Ref[IO].of(start(outbox)).flatTap(r => seen.update(_ :+ r))
                  .map(World.models(semantics, elaborated.theory.vocabulary, _))
      random <- Random.scalaUtilRandomSeedLong[IO](7)
      _      <- Interleavings[IO](semantics, worlds)(using summon, random)
                  .of(ReadRecording(Delivery.sendAll.steps)._1, List(Env.of(Values.none)))
      ends   <- seen.get.flatMap(rs => rs.traverse(_.get))
    yield ends.map(m => (Fn.as[Library](m(LibraryStore.libraryModel.name)).outbox,
      Fn.as[Map[PersonId, List[Notice]]](m(Mailer.mailerModel.name))))

  private def start(outbox: List[Notice]): Map[ModelName, ScalaValue] =
    Map(LibraryStore.libraryModel.name -> ScalaValue(library.copy(outbox = outbox)),
      Mailer.mailerModel.name -> ScalaValue(Map.empty[PersonId, List[Notice]]),
      Clock.clockModel.name -> ScalaValue(now), Pool.poolModel.name -> ScalaValue(BigInt(0)))

  private def end(m: Map[ModelName, ScalaValue]): (List[Notice], Map[PersonId, List[Notice]]) =
    (Fn.as[Library](m(LibraryStore.libraryModel.name)).outbox,
      Fn.as[Map[PersonId, List[Notice]]](m(Mailer.mailerModel.name)))

  /** Delivery on the models, its steps at once, Cat's send taking 10 ms and Bob's 60, a second of sleep a millisecond
    * (the limit 30 ms): Cat's delivered; Bob's, begun before the limit passes, finishes, and the loser is cut after
    * it, before its removal from the outbox. Each call of a model one at a time, as the models' atomic assumptions say
    * (`mailOneAtATime`, …). With the end, the notices whose sends began.
    */
  private def slowly(outbox: List[Notice], random: Random[IO])
      : IO[((List[Notice], Map[PersonId, List[Notice]]), List[Notice])] =
    for
      states <- Ref[IO].of(start(outbox))
      begun  <- Ref[IO].of(List.empty[Notice])
      one    <- Mutex[IO]
      models  = World.models(semantics, elaborated.theory.vocabulary, states)
      run    <- FlowInterpreter.concurrent(semantics, paced(models, one, begun, random))
      _      <- run.prog(ReadRecording(Delivery.run.steps)._1, Env.of(Values.none))
      after  <- states.get
      sent   <- begun.get
    yield (end(after), sent)

  /** The models, each call one at a time after its pause, each send noted to `begun` as it begins. */
  private def paced(models: World[IO], one: Mutex[IO], begun: Ref[IO, List[Notice]], random: Random[IO]): World[IO] =
    new World[IO]:
      def call(op: SymbolName, args: List[ScalaValue]): IO[ScalaValue] =
        (if op == Mailer.send.name then
           val n = Fn.as[Notice](args.head)
           begun.update(_ :+ n) *> random.betweenLong(0, 4).flatMap(ms =>
             IO.sleep((ms + (if n.to == cat then 10 else 60)).millis))
         else if op == Clock.sleep.name then IO.sleep(Fn.as[BigInt](args.head).toLong.millis)
         else IO.unit) *> one.lock.surround(models.call(op, args))
      def read(m: ModelName): IO[ScalaValue] = models.read(m)
      def write(m: ModelName, s: ScalaValue): IO[Unit] = models.write(m, s)

  /** Every end the reading allows: delivery on the models, read in turn, for each list of the scheduler's choices. */
  private def read(outbox: List[Notice]): IO[Set[(List[Notice], Map[PersonId, List[Notice]])]] =
    val choices = (0 to 8).toList.flatMap(n => List.fill(n)(List(true, false)).sequence)
    choices.traverse { races =>
      Ref[IO].of(start(outbox) + (Races.model -> ScalaValue(races))).flatMap(states =>
        FlowInterpreter.sequential(semantics, World.models(semantics, elaborated.theory.vocabulary, states))
          .prog(ReadRecording(Delivery.run.steps)._1, Env.of(Values.none)) *> states.get.map(end))
    }.map(_.toSet)

  test("delivery's time limit passes mid-send: each run leaves an end the reading allows, some half done") {
    val outbox = List(catTold, bobTold, catAgain)
    for
      random  <- Random.scalaUtilRandomSeedLong[IO](13)
      ran     <- slowly(outbox, random).map(_._1).replicateA(24)
      allowed <- read(outbox)
    yield
      assert(ran.forall(allowed), ran.filterNot(allowed).distinct.mkString("\n"))
      val (full, untouched) = ((List(catAgain), Map(cat -> List(catTold), bob -> List(bobTold))), (outbox, Map.empty))
      assert(ran.exists(e => e != full && e != untouched), s"no run was cut off half done: ${ran.distinct}")
  }

  test("a send begun when delivery's time limit passes is not cancelled part way: it finishes, its notice delivered") {
    for
      random <- Random.scalaUtilRandomSeedLong[IO](17)
      ran    <- slowly(List(catTold, bobTold, catAgain), random).replicateA(8)
    yield
      assert(ran.forall((_, sent) => sent.contains(bobTold)), "Bob's send did not begin")
      ran.foreach { case ((_, boxes), sent) =>
        assertEquals(sent.filterNot(n => boxes.getOrElse(n.to, Nil).contains(n)), Nil, boxes)
      }
  }

  test("Cat's notice delivered, its branches at once: every interleaving delivers it once") {
    interleaved(List(catTold)).map(ends => assertEquals(ends.distinct, List((Nil, Map(cat -> List(catTold))))))
  }

  test("Cat's first and Bob's go at once; Cat's second waits for the next run, whatever the interleaving") {
    interleaved(List(catTold, bobTold, catAgain)).map(ends => assertEquals(ends.distinct,
      List((List(catAgain), Map(cat -> List(catTold), bob -> List(bobTold))))))
  }
