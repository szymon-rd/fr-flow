package frflow.api
package report

import frflow.protocol.*
import io.circe.{Codec, Encoder, Json}

/** One node as `check` left it; `idle`, for a root, is what doing nothing is when it meets the root. `status` is how
  * its check ended: `proven` with an obligation still open (its `impl`, `root_impl`) is not `ok`.
  */
final case class CheckedNode(id: NodeId, status: CheckStatus, notProven: List[ObligationName], problems: List[Result],
    failing: List[FailingExample], idle: Option[String], messages: List[String], hint: Option[String]):
  /** Proven, nothing of it left open, its examples passing, and (for the root) not met by doing nothing:
    * what `check` exits 0 on.
    */
  def ok: Boolean = status == CheckStatus.Proven && notProven.isEmpty && failing.isEmpty && idle.isEmpty

object CheckedNode:
  /** Encoded with `ok`, so that `status` is not read as all of it. */
  given Codec.AsObject[CheckedNode] =
    val derived = Codec.AsObject.derived[CheckedNode]
    Codec.AsObject.from(derived, Encoder.AsObject.instance(c => derived.encodeObject(c).add("ok", Json.fromBoolean(c.ok))))

  def of(r: Reviewed, c: NodeCheck): CheckedNode =
    val failing = r.node.examples.filterNot(_.passes).map(e =>
      FailingExample(s"${if e.expected then "expect" else "reject"} ${e.call}  given ${e.`given`.mkString(", ")}  — ${e.note}",
        (e.fails.toList ++ e.codeFails.map(i => s"the implementation $i")).mkString("; ")))
    CheckedNode(r.id, c.status, c.obligations.filter(o => !o.isEvaluation && !o.fine).map(_.name), c.obligations.filterNot(_.fine),
      failing, r.node.idle, c.messages,
      // With an example failing the node may be false: no hint to prove it.
      c.hint.filter(_ => failing.isEmpty))
