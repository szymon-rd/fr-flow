package frflow.api

import frflow.api.view.diff.NodeDiff
import frflow.api.view.{Found, View}
import frflow.core.name.NodeId

/** What a front end reads: the view, a node's diff since its decision (none when the model has no such node), where
  * a change belongs, and the model's fingerprint (the sources as they are now: a process that keeps running compiled
  * its model when it started, and once this moves what it shows is not decided on). Laws: reading changes nothing;
  * `diff(id)` is defined exactly for the nodes of `view`.
  */
trait Reading[F[_]]:
  def view: F[View]
  def diff(id: NodeId): F[Option[NodeDiff]]
  def find(query: String): F[Found]
  def modelFingerprint: F[String]
