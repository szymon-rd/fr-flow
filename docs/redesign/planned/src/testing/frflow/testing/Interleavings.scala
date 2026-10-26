package frflow.testing

import cats.effect.Async
import cats.effect.std.Random
import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.name.{BoundaryName, NodeId}
import frflow.dsl.flow.Bound
import frflow.eval.Denote
import frflow.eval.run.{ExampleResult, Examples, FlowRun}
import scala.concurrent.duration.*

/** A flow with concurrent steps run from each example on the implementations, with a random pause before each call,
  * `Runs` times, each run compared with the models' sequential reading. Deterministic under `TestControl`.
  */
final class Interleavings[F[_]: Async: Random](denote: Denote, bound: Map[BoundaryName, Bound]):
  val Runs: Int = 8

  def of(r: Resolved, node: NodeId): F[List[ExampleResult]] =
    FlowRun.concurrent(denote, bound, pause).flatMap(run => Examples(denote, run).of(r, node).replicateA(Runs))
      .map(_.flatten)

  private def pause: F[Unit] = Random[F].betweenLong(0, 5).flatMap(ms => Async[F].sleep(ms.millis))
