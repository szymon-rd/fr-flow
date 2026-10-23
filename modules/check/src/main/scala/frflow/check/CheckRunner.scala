package frflow
package check

import cats.data.NonEmptyList
import cats.effect.IO
import cats.effect.syntax.all.*
import cats.syntax.all.*
import frflow.protocol.{NodeKind as _, *}

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
    (kb.parts(n) ++ g.callees(n) ++ (if a.isRoot(n) then kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
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
    ready.map(n => g.specModule(n.id)) ++ ready.filter(g.obligation(_, "impl").isDefined).map(n => g.implModule(n.id))

  /** A level's theorems, in one build. */
  def theorems(level: List[Node[?]]): List[String] =
    level.filter(n => unchanged(n).isEmpty && g.waitsForDefinition(n).isEmpty).map(n => g.theoremsModule(n.id))

  /** The status of a node's formal parts, from this run or the record. */
  def parts(n: Node[?], done: Map[String, NodeCheck]): List[(String, Option[CheckStatus])] =
    kb.parts(n).filter(g.formal).map(p => p.id -> done.get(p.id).orElse(a.current(p)).map(_.status))

  /** A node is proven with its parts: kept as it was only while they all are. */
  def kept(n: Node[?], parts: List[(String, Option[CheckStatus])]): Option[NodeCheck] =
    unchanged(n).filter(_ => parts.forall(_._2.contains(CheckStatus.Proven)))

/** Runs a plan: level by level, each level's nodes side by side (`threads` at a time). */
object CheckRunner:
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
