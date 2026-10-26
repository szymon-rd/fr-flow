package frflow
package check
package proving

import frflow.protocol.*

/** What to check, in what order: each node after what its Lean imports, a level's nodes side by side; `only`: that node alone. */
final case class CheckPlan(a: Analysis, only: Option[String]):
  private val g = a.generate
  private val kb = a.kb

  val todo: List[Node[?]] = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id))
  def unchanged(n: Node[?]): Option[NodeCheck] = a.current(n).filter(_ => only.isEmpty)
  val pending: List[Node[?]] = todo.filter(unchanged(_).isEmpty)

  /** By level: one more than the highest below it. */
  val levels: List[List[Node[?]]] =
    def below(n: Node[?]): List[Node[?]] =
      (kb.parts(n) ++ g.callees(n) ++ (if kb.isRoot(n) then kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
        .filter(x => g.formal(x) && !(x eq n))
    def go(n: Node[?], seen: Set[String], known: Map[String, Int]): (Int, Map[String, Int]) =
      known.get(n.id).fold {
        val (l, after) = below(n).filterNot(x => seen(x.id)).foldLeft((0, known)) { case ((l, k), x) =>
          val (lx, k2) = go(x, seen + n.id, k)
          (l.max(lx + 1), k2)
        }
        (l, after.updated(n.id, l))
      }(l => (l, known))
    val level = todo.foldLeft(Map.empty[String, Int])((known, n) => go(n, Set.empty, known)._2)
    todo.groupBy(n => level.getOrElse(n.id, 0)).toList.sortBy(_._1).map(_._2)

  /** The models, and the proofs of the code (which import only models), first in one build: built one at a time, they take most of a cold check. */
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
