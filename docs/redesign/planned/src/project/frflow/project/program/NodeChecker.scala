package frflow.project.program

import cats.data.{EitherT, NonEmptyList}
import cats.Monad
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.project.port.Lake
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.verdict.{Judge, Judged, NodeCheck}

/** One node's check: Lean steps, each followed by a pure judge that may end the check. */
final class NodeChecker[F[_]: Monad](lake: Lake[F]):
  private type Step[A] = EitherT[F, Judged, A]

  def apply(a: Analysis, n: NodeId): F[NodeCheck] =
    val steps: Step[Judged] =
      for
        _ <- stop(Judge.waiting(Nil))
        spec = Layout(a.valid.theory.name).ofNode(n, NodePart.Spec)
        _ <- EitherT.liftF(lake.build(NonEmptyList.one(spec))).flatMap(r => stop(Judge.model(r)))
        j <- proven(a, n)
      yield j
    Monad[F].map(steps.merge)(stamp(a, n, _))

  private def stop(j: Option[Judged]): Step[Unit] = EitherT.fromEither(j.toLeft(()))
  /** `complete` (generated or authored), `impl`, the evaluations and the tries, each a run and a judge. */
  private def proven(a: Analysis, n: NodeId): Step[Judged] = ???
  private def stamp(a: Analysis, n: NodeId, j: Judged): NodeCheck = ???
