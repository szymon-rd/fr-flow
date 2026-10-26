package frflow.api

import frflow.api.view.{CheckEvent, View}
import frflow.core.name.NodeId

/** What a front end proves with: the Lean and the snapshot written (`render`, `status`), a check whose progress
  * streams as it goes, `ci` (a check of everything, then the view), and proof stubs.
  */
trait Proving[F[_]]:
  def render: F[List[String]]
  def status: F[View]
  def check(only: Option[NodeId]): fs2.Stream[F, CheckEvent]
  def ci: fs2.Stream[F, CheckEvent]
  def scaffold(id: NodeId): F[String]
