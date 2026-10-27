package frflow.eval.flow

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.code.Values
import frflow.core.name.ModelName
import frflow.dsl.flow.{ReadRecording, Recorded}
import frflow.eval.{Env, Fn, Races, ScalaValue, Semantics}

/** A race whose sides differ, on the models: read as Lean reads it, the world's choice of the winner then only the
  * winner's steps (`races.leftWins`): the left when the world says nothing, either as its races say.
  */
class RacesSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val semantics = Semantics(elaborated)

  /** Put 1 then read, raced against put 2 then read. */
  private def raced[F[_]](s: Shelf[F, Term], f: Flow[F]): F[Term[Either[List[BigInt], List[BigInt]]]] =
    f.race(f.flatMap(s.put(1))(_ => s.items), f.flatMap(s.put(2))(_ => s.items))

  private def onModels(races: Option[List[Boolean]]): (Either[Any, Any], List[BigInt], List[Boolean]) =
    val prog = ReadRecording(raced[Recorded](Shelf.shelf.recording, summon[Flow[Recorded]]))._1
    val start = Map(Shelf.kept.name -> ScalaValue(List.empty[BigInt]), Shelf.ticks.name -> ScalaValue(BigInt(0))) ++
      races.map(Races.model -> ScalaValue(_))
    val run = for
      states <- Ref.of[IO, Map[ModelName, ScalaValue]](start)
      world   = frflow.eval.flow.World.models(semantics, elaborated.theory.vocabulary, states)
      out    <- FlowInterpreter.sequential(semantics, world).prog(prog, Env.of(Values.none))
      end    <- states.get
    yield (Fn.as[Either[Any, Any]](out), Fn.as[List[BigInt]](end(Shelf.kept.name)),
      end.get(Races.model).map(Fn.as[List[Boolean]]).getOrElse(Nil))
    run.unsafeRunSync()

  test("the world says nothing: the left wins, and only its steps run") {
    assertEquals(onModels(None), (Left(List(BigInt(1))), List(BigInt(1)), Nil))
  }

  test("the world's races say who wins, each race taking the next") {
    assertEquals(onModels(Some(List(false, true))), (Right(List(BigInt(2))), List(BigInt(2)), List(true)))
    assertEquals(onModels(Some(List(true))), (Left(List(BigInt(1))), List(BigInt(1)), Nil))
  }

  test("races is reserved: no model or boundary may take its name") {
    assert(frflow.core.analysis.Reserved.names("races"))
    assertEquals(List(Races.model.value).map(frflow.core.analysis.Reserved.names), List(true))
  }
