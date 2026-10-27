package frflow.agent.panel

import cats.effect.IO
import frflow.agent.request.{AgentRefusal, RequestId}
import frflow.agent.work.AgentApi
import frflow.api.Host
import frflow.web.{Routes, WebPart}
import io.circe.syntax.*
import io.circe.Encoder
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.dsl.io.*
import org.http4s.{HttpRoutes, Response, Status}

/** The agent layer in the web view: its routes under `/api/agent/`, behind the page's token, and its panels
  * (`agent.js`). The developer on the page asks and closes, as `developer`; nothing here decides.
  */
object AgentWeb:
  def part(host: Host[IO], developer: String, a: AgentApi[IO]): IO[WebPart] =
    IO.blocking(scala.io.Source.fromResource("frflow/agent/agent.js").mkString).map(WebPart(routes(host, developer, a),
      _))

  private def routes(host: Host[IO], developer: String, a: AgentApi[IO]): HttpRoutes[IO] = HttpRoutes.of[IO] {
    case GET -> Root / "api" / "agent" / "state"         =>
      host.api.reading.view.flatMap(a.read).flatMap(v => Ok(AgentState.of(v).asJson))
    case req @ POST -> Root / "api" / "agent" / "ask"    =>
      req.as[Asking].flatMap(x => a.ask(x.node, x.text, developer)).flatMap(answer(_))
    case req @ POST -> Root / "api" / "agent" / "close"  =>
      req.as[List[String]].flatMap(ids => a.close(ids.map(RequestId(_)))).flatMap(answer(_))
  }

  private def answer[A: Encoder](r: Either[AgentRefusal, A]): IO[Response[IO]] = r.fold(e => e match
    case AgentRefusal.UnknownNode(_) | AgentRefusal.UnknownRequest(_) | AgentRefusal.NoRequest(_) =>
      Routes.error(Status.NotFound, e.message)
    case _ => Routes.error(Status.Conflict, e.message), x => Ok(x.asJson))

