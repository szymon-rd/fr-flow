package frflow
package ledger

import frflow.protocol.*
import java.time.Instant

/** The developer's requests ("Ask for a change") and the agent's answers, as values. Pure. */
object Requests:

  /** A new request on a node (or on the idea), with an id not taken yet. */
  def ask(rs: List[Request], node: Option[NodeId], text: String, by: String, now: Instant): (List[Request], Request) =
    val r = Request(freshId(rs, now), node, text, by, stamp(now), RequestStatus.Open)
    (rs :+ r, r)

  /** Answers the request `to` with the text; given a node, the developer's open request on it, or a new
    * one from the agent (when `isNode` says it is one). The requests, and the one answered.
    */
  def answer(rs: List[Request], to: String, text: String, isNode: NodeId => Boolean, now: Instant): Either[Refusal, (List[Request], Request)] =
    val byId = rs.indexWhere(_.id == RequestId(to))
    val at = if byId >= 0 then byId else rs.indexWhere(r => r.node.contains(NodeId(to)) && r.status == RequestStatus.Open)
    val all =
      if at >= 0 then Right((rs, at))
      else if isNode(NodeId(to)) then Right(ask(rs, Some(NodeId(to)), "(from the agent)", "agent", now)._1 -> rs.size)
      else Left(Refusal.UnknownRequest(to))
    all.flatMap((all, i) => update(all, i, to)(_.copy(status = RequestStatus.Answered, answer = Some(text))))

  /** The developer closes requests: done with them, answered or not. All, or none if one is unknown. */
  def close(rs: List[Request], ids: List[RequestId]): Either[Refusal, (List[Request], List[Request])] =
    ids.filterNot(i => rs.exists(_.id == i)) match
      case Nil =>
        val closed = rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r)
        Right((closed, closed.filter(r => ids.contains(r.id))))
      case unknown => Left(Refusal.UnknownRequest(unknown.mkString(", ")))

  private def update(rs: List[Request], i: Int, to: String)(f: Request => Request): Either[Refusal, (List[Request], Request)] =
    rs.lift(i).map(f).map(r => (rs.updated(i, r), r)).toRight(Refusal.UnknownRequest(to))

  private def stamp(now: Instant): String = now.toString.take(19) + "Z"

  /** `R` and the time in base 36; the next free one when two are asked at once. */
  private def freshId(rs: List[Request], now: Instant): RequestId =
    val taken = rs.map(_.id).toSet
    Iterator.from(0).map(i => RequestId(s"R${java.lang.Long.toString(now.toEpochMilli + i, 36)}")).dropWhile(taken).next()
