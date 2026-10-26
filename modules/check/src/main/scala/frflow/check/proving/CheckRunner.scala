package frflow
package check
package proving

import cats.data.NonEmptyList
import cats.effect.IO
import cats.effect.syntax.all.*
import cats.syntax.all.*
import frflow.ledger.Store
import frflow.protocol.*
import io.circe.syntax.*
import java.nio.file.Path

/** Writes the Lean and the snapshot, and checks: a plan run level by level, each level's nodes side by side. */
object CheckRunner:
  /** Writes the generated Lean; returns the files that changed. */
  def render(a: Analysis): IO[List[String]] =
    val ws = a.ws
    val keep = a.files.keySet.map(ws.lean.resolve(_).normalize)
    for
      _ <- Disk.update(ws.lean.resolve("lakefile.toml"), a.generate.lakefile(ws.kernelPath))
      _ <- Disk.update(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
      changed <- a.files.toList.sortBy(_._1).parTraverseN(8)((rel, text) => Disk.update(ws.lean.resolve(rel), text).map(Option.when(_)(rel)))
      stale <- a.generate.layout.generatedDirs.map(ws.lean.resolve).flatTraverse(d => Disk.isDirectory(d).ifM(Disk.files(d), IO.pure(Nil)))
      _ <- stale.filterNot(p => keep(p.normalize)).traverse_(Disk.delete)
    yield changed.flatten

  def writeSnapshot(a: Analysis): IO[Path] = Store.writeJson(a.ws.snapshotFile, a.snapshot.asJson).as(a.ws.snapshotFile)

  /** Renders, checks nodes (all, or one), parts first, and records the results: the nodes checked, and the analysis then. */
  def check(a: Analysis, lake: Lake, cfg: Config, only: Option[String],
      progress: Progress => IO[Unit] = _ => IO.unit): IO[(List[(Node[?], NodeCheck)], Analysis)] =
    val plan = CheckPlan(a, only)
    // A batch that builds is built for each of its targets: their own builds are skipped (one at a time, they cost
    // about as much as Lean's start). Each node's own build then replays it, with its messages.
    def batch(targets: List[String]): IO[Set[String]] =
      NonEmptyList.fromList(targets).filter(_.size > 1)
        .fold(IO.pure(Set.empty[String]))(ts => lake.build(ts).map(r => if r.ok then targets.toSet else Set.empty))
    val levels = plan.levels.filter(_.exists(plan.unchanged(_).isEmpty))
    for
      _ <- render(a)
      _ <- progress(Progress(0, levels.size, Nil)).whenA(plan.prebuild.nonEmpty)
      pre <- batch(plan.prebuild)
      (done, _) <- plan.levels.foldLeftM((Map.empty[String, NodeCheck], pre)) { case ((done, built), level) =>
        val step = levels.indexOf(level) + 1
        progress(Progress(step, levels.size, level.filter(plan.unchanged(_).isEmpty).map(_.id))).whenA(step > 0) *>
        batch(plan.theorems(level)).map(built ++ _).flatMap { built =>
          val checker = NodeChecker(a, lake, built)
          level.parTraverseN(cfg.threads) { n =>
            val parts = plan.parts(n, done)
            plan.kept(n, parts).fold(checker.check(n, parts))(IO.pure).tupleLeft(n.id)
          }.map(rs => (done ++ rs, built))
        }
      }
      results = plan.todo.flatMap(n => done.get(n.id).map(n -> _))
      all = a.checks.filter((id, _) => a.kb.node(id.value).isDefined) ++ results.map((n, c) => NodeId(n.id) -> c)
      _ <- Inputs.saveChecks(a.ws.checksFile, all)
      consistency <- Consistent.run(a, lake).map(_.orElse(a.inputs.consistency))
      (recorded, counterexamples) <- test(a, cfg, only)
    yield (results, a.withChecks(all).withTests(recorded, counterexamples).withConsistency(consistency))

  /** Tests the code of the contracts it is not proven of, against them: those whose test is not current (or `only`). */
  def test(a: Analysis, cfg: Config, only: Option[String]): IO[(Map[NodeId, Recorded], Map[NodeId, List[Counterexample]])] =
    val todo = Tests.testable(a).filter(n => only.forall(_ == n.id) && (only.isDefined || a.tested(n).isEmpty))
    for
      found <- todo.parTraverseN(cfg.threads)(n => Tests.run(a, n, a.inputs.counterexamples.getOrElse(NodeId(n.id), Nil)).map(n -> _))
      fresh = found.collect { case (n, Some(r)) => NodeId(n.id) -> Recorded(Tests.key(a, n), r) }
      kept = a.inputs.tests.filter((id, _) => a.kb.node(id.value).exists(Testing.tests(a.kb, _)))
      recorded = kept ++ fresh
      counterexamples = Tests.kept(a.inputs.counterexamples, fresh.map((id, r) => id -> r.report))
      _ <- Tests.save(a.ws, recorded, counterexamples).whenA(fresh.nonEmpty || kept.size != a.inputs.tests.size)
    yield (recorded, counterexamples)
