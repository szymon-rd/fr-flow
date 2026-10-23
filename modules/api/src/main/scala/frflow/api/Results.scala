package frflow.api

import frflow.protocol.*
import io.circe.Codec

/** An example that fails: what it says, and what failed. */
final case class FailingExample(example: String, verdict: String) derives Codec.AsObject

/** One node as `check` left it: its status, what is not proven, the examples failing (the code or the
  * contract is wrong, which no proof fixes), what Lean said, and, for a root, what doing nothing is when it
  * meets the root.
  */
final case class CheckedNode(id: NodeId, status: CheckStatus, notProven: List[String], problems: List[Result],
    failing: List[FailingExample], idle: Option[String], messages: List[String]) derives Codec.AsObject:
  def ok: Boolean = status == CheckStatus.Proven && failing.isEmpty

/** What `check` checked, and where the knowledge base stands after. */
final case class CheckReport(nodes: List[CheckedNode], view: View) derives Codec.AsObject:
  def ok: Boolean = nodes.forall(_.ok)

/** What CI found not proven, and where the knowledge base stands. */
final case class CiReport(notProven: List[CheckedNode], view: View) derives Codec.AsObject:
  def ok: Boolean = notProven.isEmpty && view.status.ok

/** The Lean files `render` changed, and the snapshot it wrote. */
final case class Rendered(changed: List[String], snapshot: String) derives Codec.AsObject

/** The proof file `scaffold` created or added stubs to, if any. */
final case class Scaffolded(node: NodeId, file: Option[String]) derives Codec.AsObject
