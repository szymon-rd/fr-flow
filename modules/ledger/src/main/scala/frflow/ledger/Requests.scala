package frflow
package ledger

import frflow.protocol.*
import java.time.Instant

/** The developer's requests ("Ask for a change") and the agent's answers, as values. Pure. */
object Requests:
  /** A new request on a node (or on the idea); `seen`, the node's version the developer asked about. */
  def ask(rs: List[Request], node: Option[NodeId], text: String, by: String, now: Instant, seen: Option[Version] = None): (List[Request], Request) =
    // `R` and the time in base 36; the next free one when two are asked at once.
    val taken = rs.map(_.id).toSet
    val id = Iterator.from(0).map(i => RequestId(s"R${java.lang.Long.toString(now.toEpochMilli + i, 36)}")).dropWhile(taken).next()
    val r = Request(id, node, text, by, now, RequestStatus.Open, seen = seen)
    (rs :+ r, r)

  /** Answers the request `to`: by id, the open request on a node, or a new one from the agent on a node `isNode` knows. */
  def answer(rs: List[Request], to: String, text: String, isNode: NodeId => Boolean, now: Instant): Either[Refusal, (List[Request], Request)] =
    val byId = rs.indexWhere(_.id == RequestId(to))
    val at = if byId >= 0 then byId else rs.indexWhere(r => r.node.contains(NodeId(to)) && r.status == RequestStatus.Open)
    val all =
      if at >= 0 then Right((rs, at))
      else if isNode(NodeId(to)) then Right(ask(rs, Some(NodeId(to)), "(from the agent)", "agent", now)._1 -> rs.size)
      else Left(Refusal.UnknownRequest(to))
    all.flatMap((all, i) => all.lift(i).map(_.copy(status = RequestStatus.Answered, answer = Some(text), answeredAt = Some(now)))
      .map(r => (all.updated(i, r), r)).toRight(Refusal.UnknownRequest(to)))

  /** The developer closes requests, answered or not. All, or none if one is unknown. */
  def close(rs: List[Request], ids: List[RequestId]): Either[Refusal, (List[Request], List[Request])] =
    ids.filterNot(i => rs.exists(_.id == i)) match
      case Nil =>
        val closed = rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r)
        Right((closed, closed.filter(r => ids.contains(r.id))))
      case unknown => Left(Refusal.NoRequest(unknown))

/** Why a decision, or an answer to a request, is not recorded: what the developer (or the agent) reads. */
enum Refusal(val message: String):
  case NoOneDecides extends Refusal("say who decides")
  case NoReason extends Refusal("give the reason for the decision in a few words: it is kept as part of the theory")
  case MovedSinceSeen(node: NodeId) extends Refusal(s"$node changed since you looked at it: look again before deciding")
  case UnknownNode(node: NodeId) extends Refusal(s"unknown node $node")
  case NotAProposal(node: NodeId, state: ReviewState) extends Refusal(s"$node is $state: only a proposal is rejected on its own")
  case AcceptFirst(waitsFor: NodeId) extends Refusal(s"accept $waitsFor first: what rests on it is decided after it")
  case AlreadyAccepted(node: NodeId) extends Refusal(s"$node is already accepted")
  case NotBelow(node: NodeId, named: List[NodeId])
      extends Refusal(s"not among the decisions below $node that this decision can act on: ${named.mkString(", ")}")
  case NotDecided(node: NodeId, state: ReviewState) extends Refusal(s"$node is $state: only a decided node is revisited")
  case AlreadyRevisited(node: NodeId) extends Refusal(s"$node is already to revisit")
  case StillInModel(node: NodeId) extends Refusal(s"$node is still in the model: only a node removed from it is gone")
  case NothingToConfirm extends Refusal("nothing to confirm: no decision is mechanical")
  case UnknownRequest(to: String) extends Refusal(s"no request or node $to")
  case NoRequest(ids: List[RequestId]) extends Refusal(s"no request ${ids.mkString(", ")}")
  case NoNodes extends Refusal("name the nodes to accept")
  case NoText extends Refusal("say what to change")
  case NoIdea extends Refusal("there is no IDEA.md yet: the agent writes it from your conversation first")
  case NoAssumption extends Refusal("say the answer you assume (--assume TEXT): the developer can then just agree")
  case UnknownQuestion(id: String) extends Refusal(s"no question $id in the conversation")
  /** No name to decide under: none given, and the developer's key is filed under none. */
  case NoDeveloper extends Refusal("say who decides: the name your key's public half is filed under (.frflow/keys/NAME.pub)")
  /** One decision of several refused: none is recorded. */
  case Within(node: NodeId, refusal: Refusal) extends Refusal(s"$node: ${refusal.message}")

  override def toString: String = message
