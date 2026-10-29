package frflow.project.check

import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.proof.obligation.ObligationName

/** Which nodes a check judges, in levels: each node Lean is asked anything of after its parts, the callees its code
  * relies on (but those above it, which its callees' statements may be: no circle orders them), and, for a root
  * `root_impl` is asked of, every node but another such root whose code Lean proves (roots
  * proven of code are not each other's below: no circle orders them); a level's nodes side by side. With `only`,
  * that node alone.
  */
object CheckPlan:
  def levels(a: Analysis, only: Option[NodeId]): List[List[NodeId]] =
    val asked = a.obligations.map(_.node)
    only.fold(byLevel(a, asked))(id => List(List(id).filter(asked.contains)).filter(_.nonEmpty))

  /** Below `n`: what its check reads the outcome of. */
  def below(a: Analysis, n: NodeId): List[NodeId] =
    val coded = if a.rooted(n) then a.obligations.filter(_.required.exists(_.name == ObligationName.Impl)).map(_.node)
      .filterNot(a.rooted) else Nil
    val r = a.decided.theory.refinement
    val above = Walk.breadthFirst(r.parents(n), identity)(r.parents).toSet
    (r.parts(n) ++ a.decided.callsOf(n).filterNot(above) ++ coded).distinct.filterNot(_ == n)

  private def byLevel(a: Analysis, asked: List[NodeId]): List[List[NodeId]] =
    val order = Walk.postorder(asked, identity)(below(a, _).filter(asked.contains))
    val level = order.foldLeft(Map.empty[NodeId, Int])((done, n) =>
      done.updated(n, below(a, n).flatMap(done.get).maxOption.fold(0)(_ + 1)))
    asked.groupBy(level.getOrElse(_, 0)).toList.sortBy(_._1).map(_._2)
