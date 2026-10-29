package frflow.testing

import cats.effect.{IO, Ref}
import cats.effect.std.Random
import cats.effect.unsafe.implicits.global
import frflow.core.code.Values
import frflow.core.name.ModelName
import frflow.*
import frflow.eval.{Env, ScalaValue, Semantics}
import frflow.eval.flow.{AtOnce, Runs, Shelf, Shelved, World}

/** A program's concurrent steps run on the models at once, each call after a random pause, from a start, `Runs`
  * times, each on a shelf holding 3: branches that only read give the models' one answer every time; branches that
  * write outside a transaction give different answers, which one order of the steps does not show.
  */
class InterleavingsSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(elaborated)

  private def interleaved(p: Shelved[?], starts: Int): List[Any] =
    val worlds = Ref.of[IO, Map[ModelName, ScalaValue]](Map(Shelf.kept.name -> ScalaValue(List(BigInt(3))),
      Clock.clockModel.name -> ScalaValue(BigInt(0)))).map(World.models(semantics, elaborated.theory.vocabulary, _))
    val run = for
      random <- Random.scalaUtilRandomSeedLong[IO](7)
      ran    <- Interleavings[IO](semantics, worlds)(using summon, random)
        .of(Runs.recorded(p), List.fill(starts)(Env.of(Values.none)))
    yield ran.map(_.unwrap)
    run.unsafeRunSync()

  test("concurrent branches that only read give one answer, interleaved any way") {
    val answers = interleaved(AtOnce.parCollect, 1)
    assertEquals((answers.size, answers.distinct), (8, List(List(BigInt(2), BigInt(3)))))
  }

  test("the interleaved runs catch branches that share state outside a transaction, where one order does not") {
    val sharing = Shelved[(List[BigInt], List[BigInt])]("both put, then read", Nil, (Right(()), Nil, BigInt(0)))(
      [F[_]] => (s: Shelf.On[F], _: Shelf.Ticking[F], f: Flow[F]) =>
        f.parTupled(f.flatMap(s.put(1))(_ => s.items), f.flatMap(s.put(2))(_ => s.items)))
    assert(interleaved(sharing, 5).distinct.size > 1, "every interleaving gave one answer")
  }
