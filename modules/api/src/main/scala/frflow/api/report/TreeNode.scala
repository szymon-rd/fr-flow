package frflow.api
package report

import frflow.protocol.*
import io.circe.Codec

/** A node of the tree, drawn once, under its first parent; `seeAlso` are the nodes below it drawn under another. */
final case class TreeNode(node: Reviewed, seeAlso: List[NodeId], children: List[TreeNode]) derives Codec.AsObject
