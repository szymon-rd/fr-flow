package frflow.project.program

import cats.Monad
import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.eval.Denote
import frflow.eval.run.Examples
import frflow.project.pipeline.Computed

/** Running Scala before the pure phases: each node's examples, and each example and probe of a contract evaluated
  * for Lean to agree with (`Evaluations`).
  */
final class Evaluate[F[_]: Monad](examples: Examples[F], denote: Denote):
  def apply(r: Resolved): F[Computed] =
    r.theory.refinement.nodes.traverse(n => examples.of(r, n.id).map(n.id -> _))
      .map(results => Computed(results.toMap, Evaluations.of(r, denote)))
