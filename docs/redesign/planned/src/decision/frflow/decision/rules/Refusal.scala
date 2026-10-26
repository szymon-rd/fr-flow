package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.review.*

/** Why a decision is refused: returned, since the caller says it to the developer and goes on. */
enum Refusal:
  case NoOneDecides, NoReason, NoNodes, NothingToConfirm
  case UnknownNode(id: NodeId)
  case MovedSinceSeen(id: NodeId)
  case NotAProposal(id: NodeId, state: ReviewState)
  case NotDecided(id: NodeId)
  case AlreadyAccepted(id: NodeId)
  case AlreadyRevisited(id: NodeId)
  case AcceptFirst(id: NodeId)
  case NotBelow(id: NodeId, named: List[NodeId])
  case StillInModel(id: NodeId)
  case Within(id: NodeId, refusal: Refusal)
