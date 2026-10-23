package frflow.api

import frflow.protocol.*

/** The DAG laid out as a tree: each node once, under its first parent (and "also under" the others), its
  * children in the order of its parts; then the sections of what is under no parent.
  */
object Trees:
  def of(v: View, from: Option[NodeId]): Either[String, Tree] =
    val ids = v.nodes.map(_.id).toSet
    def firstParent(r: Reviewed) = r.node.parents.find(ids)
    val under: Map[NodeId, List[Reviewed]] = v.nodes.flatMap(r => firstParent(r).map(_ -> r)).groupMap(_._1)(_._2)
    val elsewhere: Map[NodeId, List[NodeId]] =
      v.nodes.flatMap(r => r.node.parents.filter(ids).drop(1).map(_ -> r.id)).groupMap(_._1)(_._2)
    def inParts[A](r: Reviewed, xs: List[A])(id: A => NodeId) =
      val order = r.node.parts.zipWithIndex.toMap
      xs.sortBy(x => order.getOrElse(id(x), Int.MaxValue))
    // `path`: the nodes above, so a cycle (a problem the model reports) stops the drawing.
    def draw(r: Reviewed, path: Set[NodeId]): TreeNode =
      TreeNode(r, r.node.parents.filter(ids).drop(1), inParts(r, elsewhere.getOrElse(r.id, Nil))(identity), v.withAgent(r),
        inParts(r, under.getOrElse(r.id, Nil))(_.id).filterNot(c => path(c.id)).map(draw(_, path + r.id)))
    val summary = Queue.summary(v)
    from match
      case Some(id) => v.node(id).toRight(s"unknown node $id").map(r => Tree(List(draw(r, Set.empty)), Nil, Nil, Nil, Nil, summary))
      case None =>
        val tops = v.nodes.filter(firstParent(_).isEmpty)
        val (main, rest) = tops.partition(v.isRoot)
        val (definitions, others) = rest.partition(_.node.kind == NodeKind.Definition)
        val (assumptions, unparented) = others.partition(_.node.kind == NodeKind.Assumption)
        def drawAll(rs: List[Reviewed]) = rs.map(draw(_, Set.empty))
        Right(Tree(drawAll(main), drawAll(assumptions), drawAll(unparented), drawAll(definitions), v.annotated.gone, summary))
