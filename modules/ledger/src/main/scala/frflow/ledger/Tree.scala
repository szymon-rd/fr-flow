package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** A node drawn in the tree, under its first parent; `alsoUnder`, its other parents. */
final case class Branch(id: NodeId, alsoUnder: List[NodeId], children: List[Branch]) derives Codec.AsObject

/** The tree from the root: each node once, under its first parent. Then the nodes under no parent
  * besides the root, the definitions, and the decided nodes gone from the model.
  */
final case class Tree(roots: List[Branch], others: List[Branch], definitions: List[Branch], gone: List[NodeId])
    derives Codec.AsObject

object Tree:
  def of(a: Annotated): Tree =
    val ids = a.nodes.map(_.id).toSet
    val under = a.nodes.flatMap(r => r.node.parents.find(ids).map(_ -> r)).groupMap(_._1)(_._2)
    def branch(r: Reviewed): Branch = Branch(r.id, r.node.parents.filter(ids).drop(1), under.getOrElse(r.id, Nil).map(branch))
    val tops = a.nodes.filter(_.node.parents.forall(p => !ids(p)))
    val (defs, others) = tops.filterNot(_.node.isRoot).partition(_.node.kind == NodeKind.Definition)
    Tree(tops.filter(_.node.isRoot).map(branch), others.map(branch), defs.map(branch), a.gone.map(_.id))
