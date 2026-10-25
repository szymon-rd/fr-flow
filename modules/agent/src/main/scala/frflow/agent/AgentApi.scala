package frflow.agent

import cats.effect.IO
import cats.syntax.all.*
import frflow.agent.conversation.{Conversation, Question, Said, Talk}
import frflow.agent.request.{Request, RequestId, Requests}
import frflow.api.{Developer, Host, View}
import frflow.ledger.JsonStore
import frflow.protocol.*
import java.nio.file.Path

/** The agent layer's operations: over the project's API for the view and the nodes, and over its own files. */
trait AgentApi:
  def read(v: View): IO[AgentView]
  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[AgentRefusal, Request]]
  /** An answer read, or a request withdrawn. */
  def close(ids: List[RequestId]): IO[Either[AgentRefusal, List[Request]]]
  /** Answers a request; given a node instead, tells the developer about work they did not ask for. */
  def answer(to: String, text: String): IO[Either[AgentRefusal, RequestId]]
  // The conversation IDEA.md is written from, as the agent records it: a record, not decisions (the developer decides IDEA.md).
  def said(text: String): IO[Either[AgentRefusal, Said]]
  /** A question the agent asked, with the answer it assumed: numbered Q1, Q2, … */
  def asked(text: String, assumed: String): IO[Either[AgentRefusal, Question]]
  /** The developer's reply to a question, as they said it in chat; a later reply stands. */
  def replied(question: String, text: String): IO[Either[AgentRefusal, Question]]

object AgentApi:
  /** The agent's files in a project: requests and the conversation, beside the ledger in `.frflow/`. */
  def requestsFile(dir: Path): Path = dir.resolve(".frflow/requests.json")
  def conversationFile(dir: Path): Path = dir.resolve(".frflow/conversation.json")

  /** Over the project `host` opens, its files under the project's directory. */
  def live(host: Host): IO[AgentApi] =
    (JsonStore.make(requestsFile(host.directory), List.empty[Request]), JsonStore.make(conversationFile(host.directory), Conversation.empty))
      .mapN(Live(host, _, _))

  private final class Live(host: Host, requests: JsonStore[List[Request]], talk: JsonStore[Conversation]) extends AgentApi:
    private val api = host.api
    def read(v: View): IO[AgentView] = (requests.load, talk.load).mapN(AgentView(v, _, _))

    def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[AgentRefusal, Request]] =
      if text.trim.isEmpty then IO.pure(Left(AgentRefusal.NoText))
      else api.view.flatMap { v =>
        node.filter(id => v.node(id).isEmpty) match
          case Some(id) => IO.pure(Left(AgentRefusal.UnknownNode(id)))
          case None =>
            val seen = node.flatMap(v.node).map(_.review.version)
            IO.realTimeInstant.flatMap(now => requests.update[AgentRefusal, Request](rs => Right(Requests.ask(rs, node, text.trim, by.name, now, seen))))
      }

    def close(ids: List[RequestId]): IO[Either[AgentRefusal, List[Request]]] = requests.update(Requests.close(_, ids))
    def answer(to: String, text: String): IO[Either[AgentRefusal, RequestId]] =
      (api.view, IO.realTimeInstant).flatMapN((v, now) =>
        requests.update(Requests.answer(_, to, text, id => v.node(id).isDefined, now))).map(_.map(_.id))

    def said(text: String): IO[Either[AgentRefusal, Said]] = IO.realTimeInstant.flatMap(now => talk.update(Talk.say(_, text, now)))
    def asked(text: String, assumed: String): IO[Either[AgentRefusal, Question]] =
      IO.realTimeInstant.flatMap(now => talk.update(Talk.ask(_, text, assumed, now)))
    def replied(question: String, text: String): IO[Either[AgentRefusal, Question]] =
      IO.realTimeInstant.flatMap(now => talk.update(Talk.reply(_, question, text, now)))
