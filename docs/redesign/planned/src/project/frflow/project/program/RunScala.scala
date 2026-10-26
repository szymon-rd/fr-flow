package frflow.project.program

import cats.effect.kernel.Sync
import frflow.core.analysis.Resolved
import frflow.core.consistency.Consistency
import frflow.core.example.Example
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.eval.Semantics
import frflow.eval.run.ExampleRun
import frflow.project.pipeline.Computed
import frflow.proof.obligation.Constant
import frflow.testing.search.Witnesses

/** Running Scala before the pure phases (the developer's code runs): each example against the code, and the search
  * for the witnesses of what must be shown possible (owner §18), from the knowledge base's generators (`drawn`) and
  * small values.
  */
final class RunScala[F[_]: Sync](semantics: Semantics, drawn: Ty => List[Value]):
  def apply(r: Resolved, examples: List[Example]): F[Computed] = Sync[F].delay {
    val search = Witnesses(semantics, r.theory, drawn)
    Computed(examples.map(e => e -> ExampleRun(semantics, r.theory).of(e)),
      Consistency.vacuity(r.theory).flatMap(v => search.of(v).map(v -> _.map(Constant(_, _)))).toMap)
  }
