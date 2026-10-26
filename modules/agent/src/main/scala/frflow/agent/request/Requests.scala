package frflow.agent
package request

import frflow.protocol.*
import java.time.Instant

/** The developer's requests ("ask for a change") and the agent's answers: each operation returns the new list. */
object Requests:
  /** A new request on a node (or on the idea); `seen`, the node's version the developer asked about. */
  def ask(rs: List[Request], node: Option[NodeId], text: String, by: String, now: Instant, seen: Option[Version] = None): (List[Request], Request) =
    // `R` and the time in base 36; the next free one when two are asked at once.
    val taken = rs.map(_.id).toSet
    val id = Iterator.from(0).map(i => RequestId(s"R${java.lang.Long.toString(now.toEpochMilli + i, 36)}")).dropWhile(taken).next()
    val r = Request(id, node, text, by, now, RequestStatus.Open, seen = seen)
    (rs :+ r, r)

  /** Answers the request `to`: by id, the open request on a node, or a new one from the agent on a node `isNode` knows. */
  def answer(rs: List[Request], to: String, text: String, isNode: NodeId => Boolean, now: Instant): Either[AgentRefusal, (List[Request], Request)] =
    val byId = rs.indexWhere(_.id == RequestId(to))
    val at = if byId >= 0 then byId else rs.indexWhere(r => r.node.contains(NodeId(to)) && r.status == RequestStatus.Open)
    val all =
      if at >= 0 then Right((rs, at))
      else if isNode(NodeId(to)) then Right(ask(rs, Some(NodeId(to)), "(from the agent)", "agent", now)._1 -> rs.size)
      else Left(AgentRefusal.UnknownRequest(to))
    all.flatMap((all, i) => all.lift(i).map(_.copy(status = RequestStatus.Answered, answer = Some(text), answeredAt = Some(now)))
      .map(r => (all.updated(i, r), r)).toRight(AgentRefusal.UnknownRequest(to)))

  /** The developer closes requests, answered or not. All, or none if one is unknown. */
  def close(rs: List[Request], ids: List[RequestId]): Either[AgentRefusal, (List[Request], List[Request])] =
    ids.filterNot(i => rs.exists(_.id == i)) match
      case Nil =>
        val closed = rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r)
        Right((closed, closed.filter(r => ids.contains(r.id))))
      case unknown => Left(AgentRefusal.NoRequest(unknown))
