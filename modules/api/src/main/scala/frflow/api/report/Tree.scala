package frflow.api
package report

import frflow.protocol.*
import io.circe.Codec

/** The DAG drawn as a tree from the root; then the assumptions and the other nodes under no parent (what code
  * calls), the definitions, and the decided nodes gone from the model.
  */
final case class Tree(main: List[TreeNode], assumptions: List[TreeNode], unparented: List[TreeNode],
    definitions: List[TreeNode], gone: List[Gone], overview: Overview) derives Codec.AsObject
