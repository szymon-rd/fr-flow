package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.review.*

/** Why a decision is refused: returned, since the caller says it to the developer and goes on. */
enum Refusal:
  case NoOneDecides, NoReason, NoNodes, NothingToConfirm
  case UnknownNode(id: NodeId)
  /** The key at hand is not listed under this name in the committed deciders' list. */
  case NotADecider(name: String)
  case MovedSinceSeen(id: NodeId)
  case NotAProposal(id: NodeId, state: ReviewState)
  case NotDecided(id: NodeId)
  case AlreadyAccepted(id: NodeId)
  case AlreadyRevisited(id: NodeId)
  case AcceptFirst(id: NodeId)
  /** Its code fails a generated case: the code, or the claim, is wrong (the CLI says which, `Cause.movedUnderCode`). */
  case CodeFails(id: NodeId)
  /** Its plain code has not been tested since it, or the code, moved: there is no evidence for it yet. */
  case NotTested(id: NodeId)
  /** The ledger no longer holds what was committed of these nodes' decisions (one taken out or changed), or what
    * was committed does not read: nothing is decided until the ledger is restored from the last commit.
    */
  case Rewritten(ids: List[NodeId])
  /** The ledger counts whole against its committed history: there is nothing for a base to accept. */
  case NothingToRebase
  case NotBelow(id: NodeId, named: List[NodeId])
  case StillInModel(id: NodeId)
  case Within(id: NodeId, refusal: Refusal)
