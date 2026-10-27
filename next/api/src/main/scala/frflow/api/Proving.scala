package frflow.api

import frflow.api.view.{CheckEvent, View}
import frflow.core.name.{NodeId, RelPath}

/** What a front end proves with: the Lean written (`render`: the modules whose text changed), the Lean and the
  * snapshot written then the view (`status`), a check (Lean, then the tests before production) whose progress streams
  * as it goes and ends with the view after it, `ci` (a check of everything, the snapshot written, then the view), and
  * a proof file's stubs (`scaffold`: the file written, none when there was nothing to add). Laws: a check's stream
  * ends with one `Done`, after a `Level` for each level of the check, in order.
  */
trait Proving[F[_]]:
  def render: F[List[String]]
  def status: F[View]
  def check(only: Option[NodeId]): fs2.Stream[F, CheckEvent]
  def ci: fs2.Stream[F, CheckEvent]
  def scaffold(id: NodeId): F[Option[RelPath]]
