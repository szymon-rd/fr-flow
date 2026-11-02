package sharing

import cats.effect.{IO, Ref}
import cats.effect.std.Random
import cats.syntax.all.*
import frflow.*
import frflow.core.code.Values
import frflow.core.name.ModelName
import frflow.dsl.flow.ReadRecording
import frflow.eval.{Env, Fn, ScalaValue, Semantics}
import frflow.eval.flow.World
import frflow.project.Projects
import frflow.testing.Interleavings
import sharing.Demo.*
import sharing.domain.*
import sharing.notifications.{Delivery, Mailer, Pool}
import sharing.store.LibraryStore

/** Section 9's interleavings of sharing, over the recorded program: delivery's sends, its branches at once, each call
  * of the models after a random pause, `Interleavings.Runs` times from each start, as today's examples of the job
  * were run; the outbox and the mailboxes every interleaving leaves are the one order's.
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
  private def interleaved(outbox: List[Notice]): IO[List[(List[Notice], Set[Mailbox])]] =
    for
      seen   <- Ref[IO].of(List.empty[Ref[IO, Map[ModelName, ScalaValue]]])
      worlds  = Ref[IO].of(Map(LibraryStore.libraryModel.name -> ScalaValue(library.copy(outbox = outbox)),
                  Mailer.mailerModel.name -> ScalaValue(List.empty[Mailbox]), Clock.clockModel.name -> ScalaValue(now),
                  Pool.poolModel.name -> ScalaValue(BigInt(0))))
                  .flatTap(r => seen.update(_ :+ r)).map(World.models(semantics, elaborated.theory.vocabulary, _))
      random <- Random.scalaUtilRandomSeedLong[IO](7)
      _      <- Interleavings[IO](semantics, worlds)(using summon, random)
                  .of(ReadRecording(Delivery.sendAll.steps)._1, List(Env.of(Values.none)))
      ends   <- seen.get.flatMap(rs => rs.traverse(_.get))
    yield ends.map(m => (Fn.as[Library](m(LibraryStore.libraryModel.name)).outbox,
      Fn.as[List[Mailbox]](m(Mailer.mailerModel.name)).toSet))

  test("Cat's notice delivered, its branches at once: every interleaving delivers it once") {
    interleaved(List(catTold)).map(ends => assertEquals(ends.distinct, List((Nil, Set(Mailbox(cat, List(catTold)))))))
  }

  test("Cat's first and Bob's go at once; Cat's second waits for the next run, whatever the interleaving") {
    interleaved(List(catTold, bobTold, catAgain)).map(ends => assertEquals(ends.distinct,
      List((List(catAgain), Set(Mailbox(cat, List(catTold)), Mailbox(bob, List(bobTold)))))))
  }
