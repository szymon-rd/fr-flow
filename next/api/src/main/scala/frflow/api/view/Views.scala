package frflow.api.view

import cats.syntax.all.*
import frflow.api.node.lean.ObligationState
import frflow.api.node.{CodeView, NodeView, Relation}
import frflow.api.view.whole.WholeView
import frflow.core.name.NodeId
import frflow.decision.review.ReviewState

/** What front ends print of a view, each a function of it: the overview, the parts beside a node, the DAG drawn as a
  * tree, and the inbox.
  */
object Views:
  /** The counts by concept; complete when there are nodes, none is gone from the model, each is accepted with nothing
    * of it unproven (its check, its parts, its code, its tests, its consistency), and each store's starting state is
    * proven to meet what always holds of it.
    */
  def overview(nodes: List[NodeView], whole: WholeView, gone: List[NodeId]): Overview = Overview(
    nodes.foldMap(n => Tally.one(n.review.standing.state)), nodes.foldMap(n => Tally.one(n.proof.state)),
    nodes.foldMap(_.code.foldMap(pieces)), whole.groups.foldMap(g => Tally.one(g.status)),
    whole.examples.foldMap(e => Tally.one(e.passes)),
    nodes.nonEmpty && gone.isEmpty && whole.starts.forall(_.check.state == ObligationState.Proven) &&
      nodes.forall(n => n.review.standing.state == ReviewState.Accepted && n.proof.unproven.isEmpty))

  private def pieces(c: CodeView): Tally[Piece] =
    c.shown.proven.foldMap(_ => Tally.one(Piece.Proven)) |+| c.shown.tested.foldMap(_ => Tally.one(Piece.Tested)) |+|
      c.shown.assumed.foldMap(_ => Tally.one(Piece.Assumed))

  /** Under each parent of `id`, the other parts that with it make the parent. */
  def beside(v: View, id: NodeId): List[(NodeId, List[NodeId])] =
    v.node(id).toList.flatMap(_.place(Relation.Parent)).map(p =>
      p -> v.node(p).toList.flatMap(_.place(Relation.Part)).filterNot(_ == id))

  /** The DAG drawn depth first, each node once with its depth, under its first parent drawn, its children in the
    * order of its parts: from `from` (nothing when the view has no such node), or else the roots in the author's
    * order, then the other nodes under no parent (the premises, what code calls) in decision order.
    */
  def tree(v: View, from: Option[NodeId]): List[(Int, NodeId)] =
    val drawn = from.fold(v.nodes.map(_.id))(id => below(v, id))
    val ids = drawn.toSet
    def firstParent(n: NodeId) = v.node(n).flatMap(_.place(Relation.Parent).find(ids))
    def draw(depth: Int, path: Set[NodeId])(n: NodeId): List[(Int, NodeId)] =
      val children = v.node(n).toList.flatMap(_.place(Relation.Part))
        .filter(c => ids(c) && firstParent(c).contains(n) && !path(c))
      (depth, n) :: children.flatMap(draw(depth + 1, path + n))
    val top = if from.isDefined then drawn.take(1)
      else v.roots.filter(ids) ++ drawn.filter(n => firstParent(n).isEmpty && !v.roots.contains(n))
    top.flatMap(draw(0, Set.empty))

  /** `id` and every node below it through its parts, each once, `id` first; nothing when there is no such node. */
  private def below(v: View, id: NodeId): List[NodeId] =
    def go(todo: List[NodeId], seen: List[NodeId]): List[NodeId] = todo match
      case Nil                           => seen.reverse
      case n :: rest if seen.contains(n) => go(rest, seen)
      case n :: rest                     => go(v.node(n).toList.flatMap(_.place(Relation.Part)) ++ rest, n :: seen)
    v.node(id).fold(Nil)(_ => go(List(id), Nil))

  /** What waits for the developer, in the order decisions are taken: each node proposed or under review whose parents
    * are none of them rejected (it waits to be moved under the node chosen instead), less those `aside` (held back by
    * a layer on top) that are not mechanical: a batch takes those.
    */
  def inbox(v: View, aside: Set[NodeId]): List[NodeId] =
    def rejected(p: NodeId) = v.node(p).exists(_.review.standing.state == ReviewState.Rejected)
    v.nodes.filter { n =>
      val state = n.review.standing.state
      (state == ReviewState.Proposed || state == ReviewState.Review) && !n.place(Relation.Parent).exists(rejected) &&
        !(aside(n.id) && n.review.notMechanical.isDefined)
    }.map(_.id)
