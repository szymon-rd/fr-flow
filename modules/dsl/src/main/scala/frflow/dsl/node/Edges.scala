package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.dsl.build.{Deferred, Fault, Site}

/** A node's links as edges of the graph; a link to a node declared after it is an error on this node. */
object Edges:
  def of(h: Head): Deferred[List[Edge]] =
    val (l, to) = (h.links, target(h.id))
    (l.refines.traverse(to).map(_.map(Edge.PartOf(h.id, _))),
      l.assumes.traverse(to).map(_.map(Edge.Assumes(h.id, _))),
      l.replaces.traverse(to).map(_.map(Edge.Replaces(h.id, _)).toList)).mapN(_ ++ _ ++ _)

  private def target(id: NodeId)(p: Parent): Deferred[NodeId] = p match
    case Parent.Declared(t)   => Deferred.pure(t)
    case Parent.DeclaredLater => Deferred.failed(Site.Node(id), Fault.DeclaredLater)
