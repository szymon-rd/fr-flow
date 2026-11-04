package frflow.agent.request

import frflow.core.name.NodeId

/** The developer's requests ("ask for a change") and the agent's answers: each operation returns the new list, and
  * what it made or changed.
  */
object Requests:
  /** A new request on a node (or on the whole idea), as asked. */
  def ask(rs: List[Request], node: Option[NodeId], text: String, asked: Asked): (List[Request], Request) =
    val taken = rs.map(_.id).toSet
    val id = Iterator.from(0).map(i => RequestId(s"R${java.lang.Long.toString(asked.at.toEpochMilli + i, 36)}"))
      .dropWhile(taken).next()
    val r = Request(id, node, text, asked, RequestStatus.Open, None)
    (rs :+ r, r)

  /** Answers the request `to`: by its id, else the open request on the node named so; on a node `isNode` knows and no
    * request is open on, a new one from the agent (work the developer did not ask for).
    */
  def answer(rs: List[Request], to: String, reply: Answer, isNode: NodeId => Boolean)
      : Either[AgentRefusal, (List[Request], Request)] =
    val at = Some(rs.indexWhere(_.id == RequestId(to))).filter(_ >= 0)
      .orElse(Some(rs.indexWhere(r => r.node.contains(NodeId(to)) && r.status == RequestStatus.Open)).filter(_ >= 0))
    val all = at.map(rs -> _).orElse(Option.when(isNode(NodeId(to)))(
      ask(rs, Some(NodeId(to)), "(from the agent)", Asked("agent", reply.at, None))._1 -> rs.size))
    all.toRight(AgentRefusal.UnknownRequest(to)).flatMap((all, i) => all.lift(i)
      .map(_.copy(status = RequestStatus.Answered, answer = Some(reply)))
      .map(r => (all.updated(i, r), r)).toRight(AgentRefusal.UnknownRequest(to)))

  /** The developer closes requests, answered or not: all, or none if one is unknown. */
  def close(rs: List[Request], ids: List[RequestId]): Either[AgentRefusal, (List[Request], List[Request])] =
    ids.filterNot(i => rs.exists(_.id == i)) match
      case Nil     =>
        val closed = rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r)
        Right((closed, closed.filter(r => ids.contains(r.id))))
      case unknown => Left(AgentRefusal.NoRequest(unknown))
