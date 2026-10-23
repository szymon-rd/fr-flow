package frflow.api

import frflow.protocol.*
import io.circe.{Codec, Decoder, Encoder}

/** How far the proofs reach: splits proven, contracts proven down to their code (with running code
  * checked against a proven define), checked by running only, or reviewed only (design nodes); and
  * how many examples Lean evaluated as Scala does.
  */
final case class Coverage(
    splits: Int,
    splitsProven: Int,
    notProvenYet: List[NodeId],
    outOfLean: List[NodeId],
    contracts: Int,
    provenDown: List[NodeId],
    runningBeside: List[RunningCode],
    checkedByRunning: List[NodeId],
    designs: List[NodeId],
    examplesEvaluated: Int,
    examplesInLean: Int,
    probes: Int,
    noneEvaluated: List[NodeId]
) derives Codec.AsObject

/** Running code checked against a contract's proven define. */
final case class RunningCode(node: NodeId, define: String, running: String) derives Codec.AsObject

/** Whether the knowledge base is complete (the CI gate), with what `status` shows besides the tree. */
final case class StatusReport(view: View, coverage: Coverage, notes: List[String], ok: Boolean) derives Codec.AsObject

/** An example that fails: what it says, and what failed. */
final case class FailingExample(example: String, verdict: String) derives Codec.AsObject

/** One node as `check` left it: its status, what is not proven, the examples failing (the code or the
  * contract is wrong, which no proof fixes), what Lean said, and, for a root, what doing nothing is when it
  * meets the root.
  */
final case class CheckedNode(id: NodeId, status: CheckStatus, notProven: List[String], problems: List[Result],
    failing: List[FailingExample], idle: Option[String], messages: List[String]) derives Codec.AsObject:
  def ok: Boolean = status == CheckStatus.Proven && failing.isEmpty

final case class CheckReport(nodes: List[CheckedNode], status: StatusReport) derives Codec.AsObject:
  def ok: Boolean = nodes.forall(_.ok)

final case class CiReport(notProven: List[CheckedNode], status: StatusReport) derives Codec.AsObject:
  def ok: Boolean = notProven.isEmpty && status.ok

/** The Lean files `render` changed, and the snapshot it wrote. */
final case class Rendered(changed: List[String], snapshot: String) derives Codec.AsObject

/** The proof file `scaffold` created or added stubs to, if any. */
final case class Scaffolded(node: NodeId, file: Option[String]) derives Codec.AsObject

/** Everything known about a node, as a document for an agent or a new engineer (see `Workflow.context`). */
final case class ContextDoc(node: NodeId, markdown: String) derives Codec.AsObject

/** Where something mentioned in a `find` is. */
enum HitKind:
  case Node, Rejected, Gone, NotModelled, Idea, Term
object HitKind:
  given Codec[HitKind] = Codec.from(
    Decoder.decodeString.emap(s => HitKind.values.find(_.toString == s).toRight(s"unknown hit $s")),
    Encoder.encodeString.contramap(_.toString))

/** Something that mentions every word asked for, with the sentence that does. */
final case class Hit(kind: HitKind, id: Option[NodeId], label: String, excerpt: Option[String]) derives Codec.AsObject

/** Where a change belongs: the nodes governing a path (none: it is governed by no node), or what mentions
  * some words.
  */
enum Found derives Codec.AsObject:
  case Governed(path: String, nodes: List[Reviewed])
  case Ungoverned(path: String)
  case Mentions(query: String, hits: List[Hit])
