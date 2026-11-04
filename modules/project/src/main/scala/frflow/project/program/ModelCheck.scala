package frflow.project.program

import cats.effect.Concurrent
import frflow.core.name.{ModelName, NodeId}
import frflow.core.Theory
import frflow.eval.Semantics
import frflow.testing.{Draw, Plan}
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.report.TestReport

/** A model's operations' plain Scala tested against the model (`implementTested(ops*)(start, observe)(calls)`), as the
  * project gives it to the checker: the node its runs are reported under, and the runs.
  */
final case class ModelCheck[F[_]](node: NodeId, run: (Plan, Draw) => F[TestReport])

object ModelCheck:
  /** One per model whose operations the FrModel gives Scala, reported by the model (`ModelRuns.reportedUnder`). */
  def of[F[_]: Concurrent](semantics: Semantics, t: Theory): List[ModelCheck[F]] =
    counted(semantics, t, _ => ModelRuns.Runs)

  /** The same, each model run at most `most` times (a port giving today's counts). */
  def counted[F[_]: Concurrent](semantics: Semantics, t: Theory, most: ModelName => Int)
      : List[ModelCheck[F]] =
    t.code.implemented.toList.sortBy(_._1.value).flatMap((m, impl) => t.vocabulary.model(m).map { model =>
      val check = ModelTests.Check(model, impl)
      ModelCheck(ModelRuns.reportedUnder(m), ModelRuns[F](check, semantics, t, most(m)).of(_, _))
    })
