package frflow
package check

import cats.data.NonEmptyList
import cats.effect.IO
import cats.effect.syntax.all.*
import cats.syntax.all.*
import frflow.ledger.Store
import frflow.protocol.*
import io.circe.syntax.*
import java.nio.file.Path

/** What to check, and in what order: a node after what its Lean imports (its parts, and the contracts its
  * code calls; the root's `root_impl` imports every proven implementation), the nodes of one level side by
  * side. A node whose formal parts did not change keeps its result.
  *
  * @param only check this node alone, whatever its last check
  */
final case class CheckPlan(a: Analysis, only: Option[String]):
  private val g = a.generate
  private val kb = a.kb

  val todo: List[Node[?]] = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id))

  /** The node's recorded check, kept if its parts are proven. */
  def unchanged(n: Node[?]): Option[NodeCheck] = a.current(n).filter(_ => only.isEmpty)

  val pending: List[Node[?]] = todo.filter(unchanged(_).isEmpty)

  private def below(n: Node[?]): List[Node[?]] =
    (kb.parts(n) ++ g.callees(n) ++ (if kb.isRoot(n) then kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
      .filter(x => g.formal(x) && !(x eq n))

  /** The level of each node: one more than the highest below it. */
  val level: Map[String, Int] =
    def go(n: Node[?], seen: Set[String], known: Map[String, Int]): (Int, Map[String, Int]) =
      known.get(n.id).fold {
        val (l, after) = below(n).filterNot(x => seen(x.id)).foldLeft((0, known)) { case ((l, k), x) =>
          val (lx, k2) = go(x, seen + n.id, k)
          (l.max(lx + 1), k2)
        }
        (l, after.updated(n.id, l))
      }(l => (l, known))
    todo.foldLeft(Map.empty[String, Int])((known, n) => go(n, Set.empty, known)._2)

  val levels: List[List[Node[?]]] = todo.groupBy(n => level.getOrElse(n.id, 0)).toList.sortBy(_._1).map(_._2)

  /** The models first, in one build Lake runs in parallel, and the proofs of the code too (each imports only
    * models): one at a time, they were most of a cold check.
    */
  val prebuild: List[String] =
    val ready = pending.filter(g.waitsForDefinition(_).isEmpty)
    ready.map(n => g.layout.spec(n.id).name) ++ ready.filter(g.obligation(_, ObligationName.Impl).isDefined).map(n => g.layout.impl(n.id).name)

  /** A level's theorems, in one build. */
  def theorems(level: List[Node[?]]): List[String] =
    level.filter(n => unchanged(n).isEmpty && g.waitsForDefinition(n).isEmpty).map(n => g.layout.theorems(n.id).name)

  /** The status of a node's formal parts, from this run or the record. */
  def parts(n: Node[?], done: Map[String, NodeCheck]): List[(String, Option[CheckStatus])] =
    kb.parts(n).filter(g.formal).map(p => p.id -> done.get(p.id).orElse(a.current(p)).map(_.status))

  /** A node is proven with its parts: kept as it was only while they all are. */
  def kept(n: Node[?], parts: List[(String, Option[CheckStatus])]): Option[NodeCheck] =
    unchanged(n).filter(_ => parts.forall(_._2.contains(CheckStatus.Proven)))

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

  /** Writes the snapshot to the workspace's `snapshotFile`. */
  def writeSnapshot(a: Analysis): IO[Path] =
    Store.write(a.ws.snapshotFile, Canonical.file(a.snapshot.asJson) + "\n").as(a.ws.snapshotFile)

  /** Renders, checks nodes (all, or one), parts first, and records the results: the nodes checked, and the
    * analysis with them recorded.
    */
  def check(a: Analysis, lake: Lake, cfg: Config, only: Option[String]): IO[(List[(Node[?], NodeCheck)], Analysis)] =
    for
      _ <- render(a)
      results <- run(CheckPlan(a, only), lake, cfg.threads)
      all = a.checks.filter((id, _) => a.kb.node(id.value).isDefined) ++ results.map((n, c) => NodeId(n.id) -> c)
      _ <- ChecksStore(a.ws.checksFile).save(all)
    yield (results, a.withChecks(all))

  def run(plan: CheckPlan, lake: Lake, threads: Int): IO[List[(Node[?], NodeCheck)]] =
    // A batch that builds is built for each of its targets: their own builds are skipped (one at a time,
    // they cost about as much as Lean's start). Each node's own build then replays it, with its messages.
    def batch(targets: List[String]): IO[Set[String]] =
      NonEmptyList.fromList(targets).filter(_.size > 1)
        .fold(IO.pure(Set.empty[String]))(ts => lake.build(ts).map(r => if r.ok then targets.toSet else Set.empty))
    for
      pre <- batch(plan.prebuild)
      (done, _) <- plan.levels.foldLeftM((Map.empty[String, NodeCheck], pre)) { case ((done, built), level) =>
        batch(plan.theorems(level)).map(built ++ _).flatMap { built =>
          val checker = NodeChecker(plan.a, lake, built)
          level.parTraverseN(threads) { n =>
            val parts = plan.parts(n, done)
            plan.kept(n, parts).fold(checker.check(n, parts))(IO.pure).tupleLeft(n.id)
          }.map(rs => (done ++ rs, built))
        }
      }
    yield plan.todo.flatMap(n => done.get(n.id).map(n -> _))
