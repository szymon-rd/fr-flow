package frflow.api
package report

import io.circe.Codec

/** What `status` shows: the view, drawn as the tree. */
final case class StatusReport(view: View, tree: Tree) derives Codec.AsObject:
  def ok: Boolean = view.ok

object StatusReport:
  def of(v: View): StatusReport = StatusReport(v, Trees.all(v))
