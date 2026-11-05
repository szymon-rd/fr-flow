package frflow.eval.flow

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.code.Values
import frflow.core.name.ModelName
import frflow.dsl.vocab.ReadRecording
import frflow.eval.{Env, Fn, Races, ScalaValue}
import frflow.eval.term.Semantics

/** A race whose sides differ, on the models: read as Lean reads it, the world's choice of the winner (`Prog.leftWins`),
  * the loser's steps until the world cancels it (`Prog.Cut`), then the winner's: the left when the world says nothing,
  * its loser cancelled at once; either as its races say, the loser cancelled where they say.
  */
class RacesSuite extends munit.FunSuite:
  private val elaborated = Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val semantics = Semantics(elaborated)

  /** Put 1 then read, raced against put 2 then read. */
  private val raced: Flow[Either[List[BigInt], List[BigInt]]] =
    Shelf.putting(1).flatMap(_ => Shelf.held).race(Shelf.putting(2).flatMap(_ => Shelf.held))

  private def onModels(races: Option[List[Boolean]]): (Either[Any, Any], List[BigInt], List[Boolean]) =
    val prog = ReadRecording(raced.steps)._1
    val start = Map(Shelf.kept.name -> ScalaValue(List.empty[BigInt]),
      Clock.clockModel.name -> ScalaValue(BigInt(0))) ++
      races.map(Races.model -> ScalaValue(_))
    val run = for
      states <- Ref.of[IO, Map[ModelName, ScalaValue]](start)
      world   = frflow.eval.flow.World.models(semantics, elaborated.theory.vocabulary, states)
      out    <- FlowInterpreter.sequential(semantics, world).prog(prog, Env.of(Values.none))
      end    <- states.get
    yield (Fn.as[Either[Any, Any]](out), Fn.as[List[BigInt]](end(Shelf.kept.name)),
      end.get(Races.model).map(Fn.as[List[Boolean]]).getOrElse(Nil))
    run.unsafeRunSync()

  test("the world says nothing: the left wins, its loser cancelled before its first step") {
    assertEquals(onModels(None), (Left(List(BigInt(1))), List(BigInt(1)), Nil))
  }

  test("the world's races say who wins, each choice taking the next") {
    assertEquals(onModels(Some(List(false, true, true))), (Right(List(BigInt(2))), List(BigInt(2)), List(true)))
    assertEquals(onModels(Some(List(true))), (Left(List(BigInt(1))), List(BigInt(1)), Nil))
  }

  test("the loser runs until the world cancels it, what it did kept: the winner sees it") {
    assertEquals(onModels(Some(List(false, false, true))),
      (Right(List(BigInt(1), BigInt(2))), List(BigInt(1), BigInt(2)), Nil))
    assertEquals(onModels(Some(List(true, false, false))),
      (Left(List(BigInt(2), BigInt(1))), List(BigInt(2), BigInt(1)), Nil))
  }

  test("races is reserved: no model may take its name") {
    assert(frflow.core.analysis.Reserved.names("races"))
    assertEquals(List(Races.model.value).map(frflow.core.analysis.Reserved.names), List(true))
  }
