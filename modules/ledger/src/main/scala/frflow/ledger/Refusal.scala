package frflow
package ledger

import frflow.protocol.*

/** Why a decision, or an answer to a request, is not recorded: what the developer (or the agent)
  * reads, and does something about.
  */
enum Refusal:
  case NoOneDecides
  case NoReason
  case MovedSinceSeen(node: NodeId)
  case UnknownNode(node: NodeId)
  case NotAProposal(node: NodeId, state: ReviewState)
  case AcceptFirst(waitsFor: NodeId)
  case AlreadyAccepted(node: NodeId)
  case NotBelow(node: NodeId, named: List[NodeId])
  case NotDecided(node: NodeId, state: ReviewState)
  case AlreadyRevisited(node: NodeId)
  case StillInModel(node: NodeId)
  case NothingToConfirm
  case UnknownRequest(to: String)
  /** An acceptance names no node. */
  case NoNodes
  /** A request says nothing. */
  case NoText
  /** No name to decide under: none given, and the developer's key is filed under none. */
  case NoDeveloper
  /** One decision of several refused: none is recorded. */
  case Within(node: NodeId, refusal: Refusal)

  def message: String = this match
    case NoOneDecides => "say who decides"
    case NoReason => "give the reason for the decision in a few words: it is kept as part of the theory"
    case MovedSinceSeen(n) => s"$n changed since you looked at it: look again before deciding"
    case UnknownNode(n) => s"unknown node $n"
    case NotAProposal(n, st) => s"$n is $st: only a proposal is rejected on its own"
    case AcceptFirst(w) => s"accept $w first: what rests on it is decided after it"
    case AlreadyAccepted(n) => s"$n is already accepted"
    case NotBelow(n, xs) => s"not among the decisions below $n that this decision can act on: ${xs.mkString(", ")}"
    case NotDecided(n, st) => s"$n is $st: only a decided node is revisited"
    case AlreadyRevisited(n) => s"$n is already to revisit"
    case StillInModel(n) => s"$n is still in the model: only a node removed from it is gone"
    case NothingToConfirm => "nothing to confirm: no decision is mechanical"
    case UnknownRequest(to) => s"no request or node $to"
    case NoNodes => "name the nodes to accept"
    case NoText => "say what to change"
    case NoDeveloper => "say who decides: the name your key's public half is filed under (.frflow/keys/NAME.pub)"
    case Within(n, r) => s"$n: ${r.message}"

  /** The model moved since the developer looked: they look again, rather than change what they asked. */
  def stale: Boolean = this match
    case MovedSinceSeen(_) => true
    case Within(_, r) => r.stale
    case _ => false

  override def toString: String = message
