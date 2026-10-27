package frflow.agent.work

import cats.Monad
import cats.effect.{Async, Clock}
import cats.syntax.all.*
import frflow.agent.conversation.{Conversation, Question, Said, Talk}
import frflow.agent.request.{AgentRefusal, Answer, Asked, Request, RequestId, Requests}
import frflow.agent.store.{FileStore, MemoryStore, Store}
import frflow.api.Reading
import frflow.api.view.View
import frflow.core.name.NodeId
import java.nio.file.Path

/** The agent layer's operations, over reading the project (the view, the nodes) and its own two files: the developer's
  * requests and the agent's answers, and the conversation. None decides: deciding stays the developer's, with their
  * key. Interpreters: the files under the project's `.frflow/` (`make`), and memory (`inMemory`).
  */
trait AgentApi[F[_]]:
  def read(v: View): F[AgentView]
  /** The developer asks for a change, on a node (as they see it now) or on the whole idea. */
  def ask(node: Option[NodeId], text: String, by: String): F[Either[AgentRefusal, Request]]
  /** An answer read, or a request withdrawn: the developer's. */
  def close(ids: List[RequestId]): F[Either[AgentRefusal, List[Request]]]
  /** The agent answers a request; given a node instead, it tells the developer of work they did not ask for. */
  def answer(to: String, text: String): F[Either[AgentRefusal, RequestId]]
  def said(text: String): F[Either[AgentRefusal, Said]]
  def asked(text: String, assumed: String): F[Either[AgentRefusal, Question]]
  def replied(question: String, text: String): F[Either[AgentRefusal, Question]]

object AgentApi:
  def requestsFile(dir: Path): Path = dir.resolve(".frflow/requests.json")
  def conversationFile(dir: Path): Path = dir.resolve(".frflow/conversation.json")

  def make[F[_]: Async](api: Reading[F], dir: Path): F[AgentApi[F]] =
    (FileStore.make(requestsFile(dir), List.empty[Request]), FileStore.make(conversationFile(dir), Conversation.empty))
      .mapN(Over(api, _, _))

  def inMemory[F[_]: Async](api: Reading[F]): F[AgentApi[F]] =
    (MemoryStore[F, List[Request]](Nil), MemoryStore[F, Conversation](Conversation.empty)).mapN(Over(api, _, _))

  private final class Over[F[_]: Monad: Clock](api: Reading[F], requests: Store[F, List[Request]],
      talk: Store[F, Conversation]) extends AgentApi[F]:
    def read(v: View): F[AgentView] = (requests.load, talk.load).mapN(AgentView(v, _, _))

    def ask(node: Option[NodeId], text: String, by: String): F[Either[AgentRefusal, Request]] =
      if text.trim.isEmpty then AgentRefusal.NoText.asLeft[Request].pure[F]
      else api.view.flatMap { v =>
        node.filter(v.node(_).isEmpty) match
          case Some(id) => AgentRefusal.UnknownNode(id).asLeft[Request].pure[F]
          case None     => Clock[F].realTimeInstant.flatMap(now => requests.update[AgentRefusal, Request](rs =>
              Right(Requests.ask(rs, node, text.trim, Asked(by, now, node.flatMap(v.node).map(_.review.version))))))
      }

    def close(ids: List[RequestId]): F[Either[AgentRefusal, List[Request]]] = requests.update(Requests.close(_, ids))

    def answer(to: String, text: String): F[Either[AgentRefusal, RequestId]] =
      (api.view, Clock[F].realTimeInstant).flatMapN((v, now) =>
        requests.update(Requests.answer(_, to, Answer(text, now), v.node(_).isDefined))).map(_.map(_.id))

    def said(text: String): F[Either[AgentRefusal, Said]] =
      Clock[F].realTimeInstant.flatMap(now => talk.update(Talk.say(_, text, now)))
    def asked(text: String, assumed: String): F[Either[AgentRefusal, Question]] =
      Clock[F].realTimeInstant.flatMap(now => talk.update(Talk.ask(_, text, assumed, now)))
    def replied(question: String, text: String): F[Either[AgentRefusal, Question]] =
      Clock[F].realTimeInstant.flatMap(now => talk.update(Talk.reply(_, question, text, now)))
