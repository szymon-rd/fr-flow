package frflow.api
package report

import io.circe.Codec

final case class CheckReport(nodes: List[CheckedNode], view: View, overview: Overview) derives Codec.AsObject:
  def ok: Boolean = nodes.forall(_.ok)
