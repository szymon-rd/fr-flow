package frflow.eval.flow

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import frflow.*
import frflow.core.code.Values
import frflow.core.expr.Prog
import frflow.core.name.ModelName
import frflow.core.term.Stated
import frflow.dsl.flow.{ReadRecording, Recorded}
import frflow.eval.{Env, Faults, Fn, Raised, Running, ScalaValue, Semantics}

/** A test program's two runs, each from an empty shelf at time 0 with the program's faults: its recording's `Prog` on
  * the models (`FlowInterpreter`, as Lean reads it), and the program itself in production (`Running`) on the models'
  * instances over `Ref`s. Each gives the outcome (`Left` its error), the shelf and the time.
  */
object Runs:
  type Seen = (Either[Any, Any], List[BigInt], BigInt)
  private val elaborated = Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val semantics = Semantics(elaborated)

  def onModels[R](p: Shelved[R]): IO[Seen] =
    val prog = recorded(p)
    for
      states <- Ref.of[IO, Map[ModelName, ScalaValue]](Map(Shelf.kept.name -> ScalaValue(List.empty[BigInt]),
        Shelf.ticks.name -> ScalaValue(BigInt(0)), Faults.model -> ScalaValue(p.faults)))
      world   = frflow.eval.flow.World.models(semantics, elaborated.theory.vocabulary, states)
      out    <- FlowInterpreter.sequential(semantics, world).outcome(prog, Env.of(Values.none))
      end    <- states.get
    yield (out.bimap(_.unwrap, _.unwrap), Fn.as[List[BigInt]](end(Shelf.kept.name)),
      Fn.as[BigInt](end(Shelf.ticks.name)))

  /** The recorded steps of a test program. */
  def recorded[R](p: Shelved[R]): Prog[Stated[?]] =
    ReadRecording(p.program[Recorded](Shelf.shelf.recording, Shelf.clock.recording, summon[Flow[Recorded]]))._1

  def running[R](p: Shelved[R]): IO[Seen] =
    for
      run    <- Running.make[IO](Values.none)
      shelf  <- IO.ref(List.empty[BigInt])
      time   <- IO.ref(BigInt(0))
      faults <- IO.ref(p.faults)
      kept    = Faulty(Kept[IO](Held(shelf, run))(using run), faults, run)
      out    <- p.program[IO](kept, Ticks[IO](Held(time, run))(using run), run).map(t => run.value(t): Any).attempt
      held   <- shelf.get
      now    <- time.get
    yield (out.leftMap { case r: Raised => r.error.unwrap; case other => throw other }, held, now)
