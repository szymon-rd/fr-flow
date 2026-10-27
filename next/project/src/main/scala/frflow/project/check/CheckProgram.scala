package frflow.project.check

import cats.effect.Clock
import cats.{MonadThrow, Parallel}
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.project.port.{FrFlowError, Lake, ProjectFiles, Records}
import frflow.proof.verdict.{CheckStatus, Checks, NodeCheck}

/** `check`: the Lean that changed written, then the nodes checked level by level (parts first, a level's nodes side
  * by side), each kept as recorded while its check is current (its key the node's now, its parts as proven as when
  * it was made), then the theory's own check unless current; the checks recorded (`checks.json`). With `only`, that
  * node is checked whatever its record. Asks only `MonadThrow`, `Parallel` and `Clock`; tested against a scripted
  * `Lake` and memory.
  */
final class CheckProgram[F[_]: MonadThrow: Parallel: Clock](files: ProjectFiles[F], lake: Lake[F], library: String):
  private val nodes = NodeChecker(lake, files)

  /** The nodes checked, in order, and the analysis with every check recorded. */
  def apply(a: Analysis, only: Option[NodeId]): F[(List[NodeCheck], Analysis)] =
    for
      _     <- lake.available.ifM(MonadThrow[F].unit, MonadThrow[F].raiseError(FrFlowError.NoLean))
      _     <- only.filterNot(a.decided.theory.node(_).isDefined)
                 .traverse_(id => MonadThrow[F].raiseError[Unit](FrFlowError.UnknownNode(id)))
      _     <- Render(files, library)(a)
      done  <- CheckPlan.levels(a, only).foldLeftM(Map.empty[NodeId, NodeCheck])((done, level) =>
                 level.parTraverse(n => kept(a, n, done, only).fold(nodes(a, n, parts(a, n, done)))(_.pure[F]))
                   .map(done ++ _.map(c => c.node -> c)))
      whole <- a.wholeCheck.fold(WholeChecker(lake)(a))(w => w.some.pure[F])
      checks = Checks(a.inputs.recorded.checks.nodes.filter((id, _) => a.decided.theory.node(id).isDefined) ++ done,
                 whole)
      _     <- Records.writeChecks(files, checks)
    yield (CheckPlan.levels(a, only).flatten.flatMap(done.get).filterNot(c => a.current(c.node).contains(c)),
      a.withRecorded(a.inputs.recorded.copy(checks = checks)))

  /** Its current check, kept while its parts are as proven as when it was made. */
  private def kept(a: Analysis, n: NodeId, done: Map[NodeId, NodeCheck], only: Option[NodeId]): Option[NodeCheck] =
    a.current(n).filter(c => !only.contains(n) && c.status != CheckStatus.Waiting &&
      !(c.status == CheckStatus.Proven && parts(a, n, done).exists(_ != CheckStatus.Proven)))

  /** Its parts' statuses: of this run, or as recorded and current. */
  private def parts(a: Analysis, n: NodeId, done: Map[NodeId, NodeCheck]): List[CheckStatus] =
    a.decided.theory.refinement.parts(n).filter(p => a.obligations.exists(_.node == p))
      .map(p => done.get(p).orElse(a.current(p)).fold(CheckStatus.Unchecked)(_.status))
