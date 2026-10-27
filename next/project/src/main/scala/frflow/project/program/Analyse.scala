package frflow.project.program

import cats.effect.Clock
import cats.{MonadThrow, Parallel}
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.analysis.{Resolve, Validate}
import frflow.core.example.Example
import frflow.eval.Semantics
import frflow.project.pipeline.{Analysis, Problems}
import frflow.project.port.RunCode
import frflow.testing.derive.Derive

/** A project analysed: the model validated (its problems raised, `Problems.Invalid`), the inputs read once
  * (`ReadInputs`), Scala run before the pure phases (`RunScala`, with the examples, through `RunCode`), and the
  * `Analysis` that holds every later phase.
  */
final class Analyse[F[_]: MonadThrow: Parallel: Clock](ports: Ports[F], run: RunCode[F], project: Project):
  def apply(e: Elaborated, examples: List[Example]): F[Analysis] =
    for
      valid    <- Validate(e).toEither.leftMap(Problems.Invalid(_)).liftTo[F]
      inputs   <- ReadInputs(ports, project)(e)
      computed <- RunScala(run, Semantics(e), Derive.of(e, examples))(Resolve(valid), examples, project.settings)
    yield Analysis(valid, inputs, computed)
