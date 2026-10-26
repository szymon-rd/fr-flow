package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.dsl.build.{Deferred, Fault, Site}

/** A node's links as edges of the graph; a link to a node declared after it is an error on this node. */
object Edges:
  def of(h: Head): Deferred[List[Edge]] =
    val l = h.links
    (l.under.traverse(target(h.id)).map(_.map(Edge.PartOf(h.id, _))),
      l.replaces.traverse(target(h.id)).map(_.map(Edge.Replaces(h.id, _)).toList),
      l.keeping.traverse(keeping(h.id))).mapN(_ ++ _ ++ _)

  private def keeping(id: NodeId)(k: Keeping): Deferred[Edge] = k match
    case Keeping.Kept(i, view)  => (target(id)(i), view).mapN(Edge.Keeps(id, _, _))
    case Keeping.Exempt(i, why) => target(id)(i).map(Edge.Exempt(id, _, why))

  private def target(id: NodeId)(p: Parent): Deferred[NodeId] = p match
    case Parent.Declared(t)   => Deferred.pure(t)
    case Parent.DeclaredLater => Deferred.failed(Site.Node(id), Fault.DeclaredLater)
