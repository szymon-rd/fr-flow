package frflow.protocol

import io.circe.Codec

/** Result of one obligation, or of a try (see `ObligationStatus`), by its name in Lean. */
final case class Result(name: String, status: ObligationStatus, detail: String = "") derives Codec.AsObject:
  /** A limit of what the node says, not an obligation: `idle` means doing nothing meets the root;
    * `restates`, that the node says what its one part says (a warning of `status`).
    */
  def isLimit: Boolean = name == "idle" || name == "restates"
  /** Lean evaluating an example as Scala does: the translation's cross-check. */
  def isEvaluation: Boolean = name.startsWith("eval") || name.startsWith("probe")
  /** Nothing to do about it: an obligation proven, a try that shows nothing wrong, or a limit. */
  def fine: Boolean = isLimit || status.fine

/** The outcome of checking one node, against the hash of what the check depends on. */
final case class NodeCheck(
    hash: Hash,
    status: CheckStatus,
    obligations: List[Result],
    messages: List[String],
    axioms: List[String],
    at: String
) derives Codec.AsObject:
  def result(name: String): Option[Result] = obligations.find(_.name == name)
