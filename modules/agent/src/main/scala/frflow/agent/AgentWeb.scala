package frflow.agent

import cats.effect.IO
import frflow.api.{Developer, Host}
import frflow.protocol.NodeId
import frflow.web.{Routes, WebPart}
import io.circe.{Codec, Encoder}
import org.http4s.{HttpRoutes, Response, Status}
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.dsl.io.*

/** The arguments of `ask` and `answer`, as the page sends them. */
final case class Asking(node: Option[NodeId], text: String) derives Codec.AsObject
final case class Answering(to: String, text: String) derives Codec.AsObject

/** The agent layer in the web view: its routes under `/api/agent/`, behind the page's token, and its panels (`agent.js`). */
object AgentWeb:
  def part(host: Host, dev: Developer, a: AgentApi): IO[WebPart] =
    IO.blocking(scala.io.Source.fromResource("frflow/agent/agent.js").mkString).map(WebPart(routes(host, dev, a), _))

  private def routes(host: Host, dev: Developer, a: AgentApi): HttpRoutes[IO] = HttpRoutes.of[IO] {
    case GET -> Root / "api" / "agent" / "state" => host.api.view.flatMap(a.read).flatMap(v => Ok(AgentState.of(v)))
    case req @ POST -> Root / "api" / "agent" / "ask" => req.as[Asking].flatMap(x => a.ask(x.node, x.text, dev)).flatMap(answer)
    case req @ POST -> Root / "api" / "agent" / "close" => req.as[List[RequestId]].flatMap(a.close).flatMap(answer[List[Request]])
    case req @ POST -> Root / "api" / "agent" / "answer" => req.as[Answering].flatMap(x => a.answer(x.to, x.text)).flatMap(answer)
  }

  private def answer[A: Encoder](r: Either[AgentRefusal, A]): IO[Response[IO]] = r.fold(e => e match
    case AgentRefusal.UnknownNode(_) | AgentRefusal.UnknownRequest(_) | AgentRefusal.NoRequest(_) => Routes.error(Status.NotFound, e.message)
    case _ => Routes.error(Status.Conflict, e.message), Ok(_))
