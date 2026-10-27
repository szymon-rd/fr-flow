package frflow.project.program

import cats.Parallel
import cats.effect.kernel.Sync
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.analysis.{Resolve, Validate}
import frflow.core.example.Example
import frflow.core.name.RelPath
import frflow.eval.Semantics
import frflow.project.pipeline.{Analysis, Problems}
import frflow.testing.Settings
import frflow.testing.derive.Derive

/** A project analysed: the model validated (its problems raised, `Problems.Invalid`), the inputs read once
  * (`ReadInputs`), Scala run before the pure phases (`RunScala`, with the examples), and the `Analysis` that holds
  * every later phase. The developer's code runs, so `Sync`.
  */
final class Analyse[F[_]: Sync: Parallel](ports: Ports[F], sources: List[RelPath], settings: Settings):
  def apply(e: Elaborated, examples: List[Example]): F[Analysis] =
    for
      valid    <- Validate(e).toEither.leftMap(Problems.Invalid(_)).liftTo[F]
      inputs   <- ReadInputs(ports, sources, settings)(e)
      computed <- RunScala(Semantics(e), Derive.of(e, examples))(Resolve(valid), examples, settings)
    yield Analysis(valid, inputs, computed)
