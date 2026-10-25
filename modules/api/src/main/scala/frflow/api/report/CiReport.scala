package frflow.api
package report

import io.circe.Codec

final case class CiReport(notProven: List[CheckedNode], view: View, tree: Tree) derives Codec.AsObject:
  def ok: Boolean = notProven.isEmpty && view.ok
