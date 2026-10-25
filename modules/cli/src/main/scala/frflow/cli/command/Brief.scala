package frflow.cli
package command

import frflow.api.*
import frflow.protocol.*
import io.circe.{Codec, Encoder, Json}
import io.circe.derivation.ConfiguredCodec
import io.circe.syntax.*

/** `--json`: a value as the API returns it, with each node in it in brief, and each decision without the content and
  * chain it was bound to (the node shown keeps its own content).
  */
trait Brief[A]:
  def apply(a: A): Json

object Brief:
  def apply[A](a: A)(using b: Brief[A]): Json = b(a)

  /** A node inside a value: without the generated Lean, contents and decisions it carries. */
  final case class NodeBrief(id: NodeId, kind: String, state: ReviewState, causes: List[Cause], status: Option[CheckStatus],
      statement: String, waitsFor: Option[NodeId], unproven: List[String]) derives Encoder.AsObject
  def node(r: Reviewed): NodeBrief =
    NodeBrief(r.id, r.node.shownKind, r.state, r.review.causes, r.node.status, r.node.content.statement, r.review.waitsFor, r.review.unproven)

  /** A view as `status` prints it: the counts, the warnings, each node. */
  final case class StatusBrief(overview: Overview, warnings: List[String], nodes: List[NodeBrief]) derives Encoder.AsObject

  // Within these, the values are encoded as the API's codecs do, but for a node and a decision.
  private given Encoder[Reviewed] = Encoder[NodeBrief].contramap(node)
  private given Encoder[Decision] = summon[ConfiguredCodec[Decision]].mapJsonObject(_.remove("content").remove("chain").remove("sig"))
  private given Encoder.AsObject[Gone] = Encoder.AsObject.derived
  private given Encoder.AsObject[Queued] = Encoder.AsObject.derived
  private given Encoder.AsObject[TreeNode] = Encoder.AsObject.derived
  private given Encoder.AsObject[Review] = Encoder.AsObject.derived
  private given Encoder.AsObject[NodeDiff] = Encoder.AsObject.derived
  private def of[A](e: Encoder[A]): Brief[A] = e(_)

  given Brief[Tree] = of(Encoder.AsObject.derived[Tree])
  /** A gone node keeps the content it was decided with: there is nothing else of it. */
  given Brief[GoneNode] = of(summon[Codec.AsObject[GoneNode]])
  given Brief[Inbox] = of(Encoder.AsObject.derived[Inbox])
  private def status(v: View, o: Overview) = StatusBrief(o, v.warnings, v.nodes.map(node)).asJson
  given Brief[StatusReport] = s => status(s.view, s.tree.overview)
  given Brief[CheckReport] = r => Json.obj("checked" -> r.nodes.asJson, "status" -> status(r.view, r.overview))

  /** A node's details: the node itself in full, less its generated Lean; the nodes around it in brief. */
  given Brief[NodeDetails] =
    val around = Encoder.AsObject.derived[NodeDetails]
    d =>
      val n = d.node.node.copy(lean = "", holds = "", obligations = Nil, proof = None)
      val full = Json.obj("node" -> n.asJson, "review" -> d.node.review.asJson)
      Json.fromJsonObject(("node" -> full) +: around.encodeObject(d).remove("node"))
