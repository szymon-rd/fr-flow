package frflow.project.program

import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.project.port.{Lake, ProjectFiles}
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print
import frflow.proof.verdict.NodeCheck

/** `check`: the Lean that changed written, then the nodes whose check key moved checked level by level (parts first,
  * a level's nodes side by side). Asks only `Monad` and `Parallel`; tested against a scripted `Lake` and memory.
  */
final class CheckProgram[F[_]: Monad: Parallel](files: ProjectFiles[F], lake: Lake[F]):
  def apply(a: Analysis, only: Option[NodeId]): F[(List[NodeCheck], Analysis)] =
    for
      _    <- render(a)
      done <- CheckPlan.levels(a, only).foldLeftM(List.empty[NodeCheck])((acc, level) =>
                level.parTraverse(NodeChecker(lake)(a, _)).map(acc ++ _))
    yield (done, a.withRecorded(recorded(a, done)))

  private def recorded(a: Analysis, done: List[NodeCheck]) =
    a.inputs.recorded.copy(checks = a.inputs.recorded.checks ++ done.map(c => c.node -> c))

  /** Writes each generated module whose text changed; the modules written. */
  def render(a: Analysis): F[List[ModuleName]] =
    a.modules.parTraverseFilter(m =>
      files.writeIfChanged(m.name.file, Print.module(m)).map(Option.when(_)(m.name)))

