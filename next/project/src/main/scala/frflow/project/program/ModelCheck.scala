package frflow.project.program

import cats.effect.Ref
import cats.{Id, MonadThrow}
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.dsl.model.AdapterCheck
import frflow.eval.Semantics
import frflow.testing.{Draw, Plan}
import frflow.testing.model.ModelRuns
import frflow.testing.report.TestReport

/** A store's implementation tested against its model (`stored.checkedAgainst(…)`, `stored.implementedBy(…)`), as the
  * project gives it to the checker: the assumption that the store behaves as its model, and the runs.
  */
final case class ModelCheck[F[_]](node: NodeId, run: (Plan, Draw) => F[TestReport])

object ModelCheck:
  /** Under the assumption saying the store behaves as the check's model; none when no assumption says it. */
  def of[F[_]: MonadThrow: Ref.Make, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A],
      semantics: Semantics, t: Theory): Option[ModelCheck[F]] =
    val model = check.model.stateModel
    t.nodes.map(_.node).find(_.statement.outside.contains(OutsideFact.BehavesAs(model.boundary, model.name)))
      .map(n => ModelCheck(n.id, ModelRuns(check, semantics, t).of(_, _)))
