package frflow.eval.flow

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.code.Values
import frflow.core.name.ModelName
import frflow.dsl.flow.ReadRecording
import frflow.eval.{Env, Fn, Races, ScalaValue, Semantics}

import RaceProbe.*

/** The step 13 review's race probe (B1): in production the sleep wins and the first add has landed; read as Lean
  * reads it, a race's loser runs until the scheduler cancels it between two of its steps, so the same run is one of
  * the reading's (`Prog.Cut`), and the claim that the box is untouched when the sleep wins has a counterexample.
  */
class RaceProbeSuite extends munit.FunSuite:
  private val elaborated = knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val semantics = Semantics(elaborated)

  test("production: the sleep wins, and the add it cancelled has changed the box") {
    (for
      b   <- SlowBox.holding(Nil)
      w   <- fast(0)
      run <- knowledge.running[IO](box := b, Clock.clockModel := w)
      out <- run(racerCode)
      xs  <- b.numbers
    yield assertEquals((out, xs), (Right(()), List(BigInt(1))))).unsafeRunSync()
  }

  /** The racer on the models, the scheduler's choices `races`: the box, the result, and the choices left. */
  private def onModels(races: List[Boolean]): IO[(Either[Any, Any], List[BigInt], List[Boolean])] =
    val prog = ReadRecording(racing.steps)._1
    val start = Map(box.name -> ScalaValue(List.empty[BigInt]), Clock.clockModel.name -> ScalaValue(BigInt(0)),
      Races.model -> ScalaValue(races))
    for
      states <- Ref.of[IO, Map[ModelName, ScalaValue]](start)
      world   = frflow.eval.flow.World.models(semantics, elaborated.theory.vocabulary, states)
      out    <- FlowInterpreter.sequential(semantics, world).prog(prog, Env.of(Values.none))
      end    <- states.get
    yield (Fn.as[Either[Any, Any]](out), Fn.as[List[BigInt]](end(box.name)), Fn.as[List[Boolean]](end(Races.model)))

  test("read as Lean reads it, the sleep wins after the first add: production's run, the claim's counterexample") {
    onModels(List(false, false, true, true)).map(r => assertEquals(r, (Right(()), List(BigInt(1)), List(true))))
      .unsafeRunSync()
  }

  test("the loser cancelled before its first step changes nothing, and run to its end changes all it would") {
    (for
      none <- onModels(List(false, true))
      all  <- onModels(List(false, false, false))
      left <- onModels(List(true, true))
    yield
      assertEquals(none, (Right(()), Nil, Nil))
      assertEquals(all, (Right(()), List(BigInt(1), BigInt(2)), Nil))
      assertEquals(left, (Left(()), List(BigInt(1), BigInt(2)), Nil))
    ).unsafeRunSync()
  }
