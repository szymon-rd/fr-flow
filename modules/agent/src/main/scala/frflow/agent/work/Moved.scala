package frflow.agent.work

import frflow.agent.request.{Request, RequestStatus}
import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Decision}

/** What the developer did since the agent last looked, as `wait` reports it: a node accepted (or kept), rejected
  * (with why), sent back to be revisited (with why), or agreed gone; a request asked. Read off the ledger and the
  * requests as they are on disk, so whatever model the waiting process compiled.
  */
enum Moved:
  case Accepted(node: NodeId, by: String)
  case Rejected(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, by: String, reason: String)
  case Gone(node: NodeId, by: String)
  case Asked(request: Request)

object Moved:
  /** Each decision `after` holds that `before` did not, node by node in name order; then each request open in
    * `after` that was not asked in `before`. Nothing when nothing moved.
    */
  def between(before: (Map[NodeId, List[Decision]], List[Request]),
      after: (Map[NodeId, List[Decision]], List[Request])): List[Moved] =
    val decided = after._1.toList.sortBy(_._1.value).flatMap((id, ds) =>
      ds.drop(before._1.getOrElse(id, Nil).size).map(of(id, _)))
    decided ++ after._2.filter(q => q.status == RequestStatus.Open && !before._2.exists(_.id == q.id)).map(Asked(_))

  private def of(id: NodeId, d: Decision): Moved = d.action match
    case Action.Accept | Action.Confirm => Accepted(id, d.author.by)
    case Action.Reject                  => Rejected(id, d.author.by, d.reason.text)
    case Action.Revisit                 => Revisit(id, d.author.by, d.reason.text)
    case Action.Remove                  => Gone(id, d.author.by)
