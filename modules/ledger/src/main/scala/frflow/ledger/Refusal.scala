package frflow
package ledger

import frflow.protocol.*

/** Why a decision, or an answer to a request, is not recorded: what the developer (or the agent)
  * reads, and does something about.
  */
enum Refusal:
  case NoOneDecides
  case UnknownDecision(action: Action)
  case NoReason
  case MovedSinceSeen(node: NodeId)
  case UnknownNode(node: NodeId)
  case NotAProposal(node: NodeId, state: ReviewState)
  case AcceptFirst(waitsFor: NodeId)
  case NotAlternatives(node: NodeId, named: List[NodeId])
  case AlreadyAccepted(node: NodeId)
  case NotBelow(node: NodeId, named: List[NodeId])
  case RevisitedAndConfirmed
  case ConfirmBefore(node: NodeId, first: NodeId)
  case NotOnlyAbove(node: NodeId, causes: List[Cause])
  case NotDecided(node: NodeId, state: ReviewState)
  case AlreadyRevisited(node: NodeId)
  case StillInModel(node: NodeId)
  case NotMechanical(node: NodeId, why: String)
  case NothingToConfirm
  case UnknownRequest(to: String)
  /** One decision of several refused: none is recorded. */
  case Within(node: NodeId, refusal: Refusal)

  def message: String = this match
    case NoOneDecides => "say who decides"
    case UnknownDecision(a) => s"unknown decision $a: the developer accepts or rejects"
    case NoReason => "give the reason for the decision in a few words: it is kept as part of the theory"
    case MovedSinceSeen(n) => s"$n changed since you looked at it: look again before deciding"
    case UnknownNode(n) => s"unknown node $n"
    case NotAProposal(n, st) => s"$n is $st: only a proposal is rejected on its own"
    case AcceptFirst(w) => s"accept $w first: what rests on it is decided after it"
    case NotAlternatives(n, bad) => s"not an alternative to $n: ${bad.mkString(", ")}"
    case AlreadyAccepted(n) => s"$n is already accepted"
    case NotBelow(n, xs) => s"not among the decisions below $n that this decision can act on: ${xs.mkString(", ")}"
    case RevisitedAndConfirmed => "a node is either revisited or confirmed"
    case ConfirmBefore(c, p) => s"$c cannot be confirmed before $p: confirm $p too, or decide $c after it"
    case NotOnlyAbove(c, cs) => s"$c is under review for ${cs.mkString(", ")}, not only a change above: decide it on its own"
    case NotDecided(n, st) => s"$n is $st: only a decided node is revisited"
    case AlreadyRevisited(n) => s"$n is already to revisit"
    case StillInModel(n) => s"$n is still in the model: only a node removed from it is gone"
    case NotMechanical(n, why) => s"$n is not mechanical ($why): decide it on its own"
    case NothingToConfirm => "nothing to confirm: no decision is mechanical"
    case UnknownRequest(to) => s"no request or node $to"
    case Within(n, r) => s"$n: ${r.message}"

  /** The model moved since the developer looked: they look again, rather than change what they asked. */
  def stale: Boolean = this match
    case MovedSinceSeen(_) => true
    case Within(_, r) => r.stale
    case _ => false

  override def toString: String = message
