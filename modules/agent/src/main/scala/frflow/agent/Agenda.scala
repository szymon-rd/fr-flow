package frflow.agent

import frflow.ledger.{Idea, IdeaDecision}
import frflow.protocol.*
import io.circe.Codec
import java.time.Instant

/** Why a request, an answer or a record of the conversation is not kept: what the developer or the agent reads. */
enum AgentRefusal(val message: String):
  case UnknownNode(node: NodeId) extends AgentRefusal(s"unknown node $node")
  case UnknownRequest(to: String) extends AgentRefusal(s"no request or node $to")
  case NoRequest(ids: List[RequestId]) extends AgentRefusal(s"no request ${ids.map(_.value).mkString(", ")}")
  case NoText extends AgentRefusal("say what to change")
  case NoAssumption extends AgentRefusal("say the answer you assume (--assume TEXT): the developer can then just agree")
  case UnknownQuestion(id: String) extends AgentRefusal(s"no question $id in the conversation")
  override def toString: String = message

/** The developer's requests ("ask for a change") and the agent's answers, as values. Pure. */
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

/** The conversation as the agent records it. Pure: each returns the new record, or why not. */
object Talk:
  def say(c: Conversation, text: String, now: Instant): Either[AgentRefusal, (Conversation, Said)] =
    nonEmpty(text).map { t =>
      val s = Said(t, now)
      (c.copy(said = c.said :+ s), s)
    }

  /** A question with the answer the agent assumed: numbered Q1, Q2, … in the order asked. */
  def ask(c: Conversation, text: String, assumed: String, now: Instant): Either[AgentRefusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      a <- nonEmpty(assumed).left.map(_ => AgentRefusal.NoAssumption)
    yield
      val q = Question(s"Q${c.questions.size + 1}", t, a, now)
      (c.copy(questions = c.questions :+ q), q)

  /** The developer's reply, as said in chat: a later one stands (the earlier ones are kept). */
  def reply(c: Conversation, id: String, text: String, now: Instant): Either[AgentRefusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      q <- c.question(id).toRight(AgentRefusal.UnknownQuestion(id))
    yield
      val answered = q.copy(replies = q.replies :+ Reply(t, now))
      (c.copy(questions = c.questions.map(x => if x.id == q.id then answered else x)), answered)

  private def nonEmpty(text: String): Either[AgentRefusal, String] = Option(text.trim).filter(_.nonEmpty).toRight(AgentRefusal.NoText)

/** IDEA.md against the conversation it was written from: its `From:` lines name the questions a section comes from. */
object IdeaSources:
  /** The questions each section (by heading; "" for the lead) names on its `From:` lines. */
  def of(idea: String): List[(String, List[String])] =
    val (lead, sections) = Idea.sections(idea)
    def named(text: String) =
      text.linesIterator.collect { case IdeaDecision.FromLine(ids) => ids.split("[,\\s]+").toList.filter(_.nonEmpty) }.flatten.toList
    (("" -> named(lead)) :: sections.map((h, body) => h -> named(body))).filter(_._2.nonEmpty)

  /** What the conversation says of IDEA.md now: a section naming a question there is not, and the sections whose answers
    * changed after IDEA.md was accepted (they need a look, and then IDEA.md is accepted again).
    */
  def warnings(idea: String, talk: Conversation, accepted: Option[Decision]): List[String] =
    val srcs = of(idea)
    def where(h: String) = if h.isEmpty then "the lead of IDEA.md" else s"the section \"$h\" of IDEA.md"
    val unknown = srcs.flatMap((h, ids) =>
      ids.filter(talk.question(_).isEmpty).map(q => s"${where(h)} comes from $q, which the conversation does not have"))
    val changed = accepted.toList.flatMap(d => srcs.flatMap((h, ids) =>
      ids.flatMap(talk.question).filter(q => q.replies.size > 1 && q.answeredAt.exists(_.isAfter(d.at)))
        .map(q => s"the answer to ${q.id} changed after IDEA.md was accepted: look again at ${where(h)}, which comes from it")))
    unknown ++ changed.distinct

/** What is the agent's to do: replace a rejected node (or remove it), revisit a node, move one resting on a rejected one. */
enum ForAgent derives Codec.AsObject:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])

object Tasks:
  /** A revisit is the agent's until it answers on the node (`answer NODE`), or changes it. */
  def of(a: Annotated, requests: List[Request]): List[ForAgent] =
    def last(r: Reviewed, action: Action) = r.review.history.reverse.find(_.action == action)
    def answeredSince(r: Reviewed, d: Decision) = requests.exists(q => q.node.contains(r.id) && q.answeredAt.exists(!_.isBefore(d.at)))
    val rejected = a.nodes.filter(_.state == ReviewState.Rejected)
      .flatMap(r => last(r, Action.Reject).map(d => ForAgent.Replace(r.id, d.by, d.reason)))
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit))
      .flatMap(r => last(r, Action.Revisit).filterNot(answeredSince(r, _)).map(d => ForAgent.Revisit(r.id, d.reason)))
    val moves = a.nodes.map(r => r -> frflow.ledger.Waiting.rejectedParents(a, r)).collect { case (r, ps) if ps.nonEmpty => ForAgent.Move(r.id, ps) }
    rejected ++ revisits ++ moves
