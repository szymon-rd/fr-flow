package frflow.api

import frflow.api.view.{Found, NodeDiff, View}
import frflow.core.name.NodeId

/** What a front end reads: the view, a node's diff since its decision, where a change belongs, the model's
  * fingerprint. */
trait Reading[F[_]]:
  def view: F[View]
  def diff(id: NodeId): F[Option[NodeDiff]]
  def find(query: String): F[Found]
  def modelFingerprint: F[String]
