package frflow.cli.say

import frflow.core.name.NodeId
import frflow.decision.review.{Cause, ReviewState}
import frflow.decision.rules.Refusal

/** Why a decision is refused, in words; `causes` says what moved under each node (`Cause.movedUnderCode`: a case
  * its code now fails is the claim's change, said so).
  */
object Refusals:
  def text(r: Refusal, causes: NodeId => List[Cause]): String = r match
    case Refusal.CodeFails(id)        => codeFails(id, causes(id))
    case Refusal.Within(id, inner)    => s"$id: ${text(inner, causes)}"
    case other                        => (asked orElse standing)(other)

  private val asked: PartialFunction[Refusal, String] =
    case Refusal.NoOneDecides         =>
      "who decides? pass --as NAME (or set FRFLOW_AS): your key is listed under no name in the committed deciders' list"
    case Refusal.NoReason             => "give a reason of at least three words: it is kept as part of the theory"
    case Refusal.NoNodes              => "name the nodes to accept"
    case Refusal.NothingToConfirm     => "nothing is mechanical: there is nothing to confirm"
    case Refusal.UnknownNode(id)      => s"unknown node $id"
    case Refusal.NotADecider(name)    =>
      s"your key is not listed under $name in the committed deciders' list: $name cannot decide here"

  private val standing: PartialFunction[Refusal, String] =
    case Refusal.MovedSinceSeen(id)   => s"$id changed since you saw it: look at it again"
    case Refusal.NotAProposal(id, s)  => s"$id is not a proposal: it is ${state(s)}"
    case Refusal.NotDecided(id)       => s"$id is not decided yet: there is nothing to revisit"
    case Refusal.AlreadyAccepted(id)  => s"$id is accepted already"
    case Refusal.AlreadyRevisited(id) => s"$id is to be revisited already"
    case Refusal.AcceptFirst(id)      => s"decide $id first: what rests on it is decided after it"
    case Refusal.NotTested(id)        =>
      s"$id's code is not tested yet since it, or the code, moved: run check (there is no evidence for it yet)"
    case Refusal.Rewritten(ids)       => s"the ledger no longer holds what was committed of ${ids.mkString(", ")}: " +
        "restore .frflow/ledger.json from the last commit, or have a listed decider accept it as it is (rebase)"
    case Refusal.NotBelow(id, named)  => s"not decisions below $id: ${named.mkString(", ")}"
    case Refusal.StillInModel(id)     => s"$id is still in the model: only a node gone from it is agreed gone"

  /** Not tested yet is not failing: a failing case is said apart, as the claim's change when the code did not move. */
  private def codeFails(id: NodeId, causes: List[Cause]): String =
    if Cause.movedUnderCode(causes) then
      s"$id changed and its code did not: the code fails a generated case of the changed claim " +
        "(fix the code, or the claim; check shows the case)"
    else s"$id's code fails a generated case: the code, or the claim, is wrong (check shows the case)"

  def state(s: ReviewState): String = s match
    case ReviewState.Proposed => "proposed"
    case ReviewState.Accepted => "accepted"
    case ReviewState.Review   => "to review"
    case ReviewState.Rejected => "rejected"
