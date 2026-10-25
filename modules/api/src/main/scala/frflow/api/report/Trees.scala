package frflow.api
package report

import frflow.protocol.*

object Trees:
  /** The whole DAG: each node once, under its first parent; its children in the order of its parts. */
  def all(v: View): Tree =
    val ids = v.nodes.map(_.id).toSet
    val draw = drawing(v, ids)
    val (main, rest) = v.nodes.filterNot(_.node.parents.exists(ids)).partition(v.isRoot)
    val (definitions, others) = rest.partition(_.node.kind == NodeKind.Definition)
    val (assumptions, unparented) = others.partition(_.node.kind == NodeKind.Assumption)
    Tree(main.map(draw), assumptions.map(draw), unparented.map(draw), definitions.map(draw), v.annotated.gone, Overview.of(v))

  /** What is below a node, drawn from it; none if there is no such node. */
  def from(v: View, id: NodeId): Option[Tree] =
    val children = v.nodes.flatMap(r => r.node.parents.map(_ -> r.id)).groupMap(_._1)(_._2)
    val below = Walk.preorder(List(id), identity)(children.getOrElse(_, Nil)).toSet
    v.node(id).map(r => Tree(List(drawing(v, below)(r)), Nil, Nil, Nil, Nil, Overview.of(v)))

  /** Draws the nodes among `ids`: each under its first parent among them. */
  private def drawing(v: View, ids: Set[NodeId]): Reviewed => TreeNode =
    def firstParent(r: Reviewed) = r.node.parents.find(ids)
    val drawn = v.nodes.filter(r => ids(r.id))
    val under = drawn.flatMap(r => firstParent(r).map(_ -> r)).groupMap(_._1)(_._2)
    val elsewhere = drawn.flatMap(r => r.node.parents.filter(ids).drop(1).map(_ -> r.id)).groupMap(_._1)(_._2)
    def inParts[A](r: Reviewed, xs: List[A])(id: A => NodeId) =
      val order = r.node.parts.zipWithIndex.toMap
      xs.sortBy(x => order.getOrElse(id(x), Int.MaxValue))
    // `path`: the nodes above, so a cycle (a problem the model reports) stops the drawing.
    def draw(path: Set[NodeId])(r: Reviewed): TreeNode =
      TreeNode(r, inParts(r, elsewhere.getOrElse(r.id, Nil))(identity),
        inParts(r, under.getOrElse(r.id, Nil))(_.id).filterNot(c => path(c.id)).map(draw(path + r.id)))
    draw(Set.empty)
