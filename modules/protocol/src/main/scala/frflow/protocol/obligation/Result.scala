package frflow.protocol
package obligation

import io.circe.Codec

final case class Result(name: ObligationName, status: ObligationStatus, detail: String = "") derives Codec.AsObject:
  def isEvaluation: Boolean = name.isEvaluation
  /** Nothing to do about it: an obligation proven, a try that shows nothing wrong, or a limit of what the
    * node says (doing nothing meets the root, or the node says what its one part says, or a part one of its conjuncts).
    */
  def fine: Boolean = status.fine || PartialFunction.cond(name) {
    case ObligationName.Tried(TryKind.Idle | TryKind.Restates | TryKind.RestatesConjunct(_, _)) => true
  }
