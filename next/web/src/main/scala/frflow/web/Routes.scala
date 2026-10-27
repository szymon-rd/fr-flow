package frflow.web

import cats.data.Kleisli
import cats.effect.IO
import cats.syntax.all.*
import frflow.api.FrFlowApi
import frflow.api.view.{CheckEvent, Stop, Views}
import frflow.core.name.NodeId
import frflow.decision.rules.{Command, Refusal}
import frflow.web.json.Asked.given
import frflow.web.json.Leaves.given
import frflow.web.json.ViewCodecs.given
import io.circe.syntax.*
import io.circe.{Encoder, Json}
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.dsl.io.*
import org.http4s.headers.`Content-Type`
import org.http4s.{EntityEncoder, HttpApp, HttpRoutes, MediaType, MessageFailure, QueryParamDecoder, Response, Status,
  StaticFile}
import org.typelevel.ci.CIString

/** One route per operation of the API, its views as JSON, all behind the session's token (`Gate`). Decisions are
  * `developer`'s, signed by the API as the CLI's are (an acceptance checked and tested afresh first), and refused
  * once the model's sources moved since `serve` started. `layers`: what the layers on top add (their routes, behind
  * the same token; their scripts, served as `/ext.js`).
  */
final class Routes(api: FrFlowApi[IO], developer: String, gate: Gate, layers: List[WebPart]):
  import Routes.*

  val app: HttpApp[IO] = Kleisli(req =>
    if !gate.admits(req.headers.get(CIString(TokenHeader)).map(_.head.value).orElse(req.params.get("token"))) then
      error(Status.Forbidden, NoToken)
    else layers.map(_.routes).foldLeft(routes)(_ <+> _)(req).getOrElseF(error(Status.NotFound,
      s"no route ${req.method} ${req.uri.path}")).handleErrorWith(failed))

  private def modelChanged: IO[Boolean] = api.reading.modelFingerprint.map(_ != gate.started)

  private val routes: HttpRoutes[IO] = HttpRoutes.of[IO] {
    case req @ GET -> Root                     =>
      StaticFile.fromResource[IO]("/frflow/web/index.html", Some(req)).getOrElseF(error(Status.NotFound, "no page"))
    case GET -> Root / "ext.js"                => script
    case GET -> Root / "api" / "serving"       => modelChanged.flatMap(c => Ok(Serving(developer, c)))
    case GET -> Root / "api" / "view"          => api.reading.view.flatMap(Ok(_))
    case GET -> Root / "api" / "tree" :? From(from) => api.reading.view.flatMap(v =>
        Ok(Views.tree(v, from).map((depth, id) => Json.obj("depth" -> depth.asJson, "node" -> id.asJson))))
    case GET -> Root / "api" / "inbox"         => api.reading.view.flatMap(v => Ok(Views.inbox(v, Set.empty)))
    case GET -> Root / "api" / "diff" / id     => api.reading.diff(NodeId(id)).flatMap(_.fold(error(Status.NotFound,
        s"unknown node $id"))(Ok(_)))
    case GET -> Root / "api" / "find" :? Words(q) => api.reading.find(q).flatMap(Ok(_))
    case GET -> Root / "api" / "status"        => api.proving.status.flatMap(Ok(_))
    case POST -> Root / "api" / "render"       => api.proving.render.flatMap(Ok(_))
    case POST -> Root / "api" / "check" :? From(node) => api.proving.check(node).compile.toList.flatMap(events =>
        events.collectFirst { case CheckEvent.Done(ids, v) =>
          Ok(Json.obj("checked" -> ids.asJson, "view" -> v.asJson))
        }
          .getOrElse(error(Status.InternalServerError, "the check ended without its view")))
    case req @ POST -> Root / "api" / "preview" => req.as[Command].flatMap(api.deciding.preview(_, developer))
        .flatMap(answer)
    case req @ POST -> Root / "api" / "decide"  => req.as[Command].flatMap(c => modelChanged.ifM(
        error(Status.Conflict, ModelChanged), api.deciding.decide(c, developer).flatMap(answer)))
  }

  /** The layers' scripts, as text (the JSON encoder in scope would quote it). */
  private def script: IO[Response[IO]] = IO.pure(Response[IO](Status.Ok)
    .withEntity(layers.map(_.script).mkString("\n;\n"))(using EntityEncoder.stringEncoder[IO])
    .withContentType(`Content-Type`(MediaType.application.javascript)))

object Routes:
  val TokenHeader = "X-FrFlow-Token"
  val NoToken = "no session token: open the link `sbt \"PROJECT/serve\"` printed"
  val ModelChanged = "the model changed: restart serve (what is on disk is no longer what this server compiled)"

  private given QueryParamDecoder[NodeId] = QueryParamDecoder[String].map(NodeId(_))
  private object From extends OptionalQueryParamDecoderMatcher[NodeId]("node")
  private object Words extends QueryParamDecoderMatcher[String]("q")

  /** `{"error": message}`, the body of a failure in words. */
  def error(status: Status, message: String): IO[Response[IO]] =
    IO.pure(Response[IO](status).withEntity(Json.obj("error" -> message.asJson)))

  /** A refusal is a 409 (an unknown node a 404), `{"refusal": …}`; what it records otherwise. */
  def answer[A: Encoder](r: Either[Refusal, A]): IO[Response[IO]] = r.fold(x =>
    IO.pure(Response[IO](x match
      case Refusal.UnknownNode(_) => Status.NotFound
      case _                      => Status.Conflict).withEntity(Json.obj("refusal" -> x.asJson))), Ok(_))

  /** What stops an operation, `{"stop": …}`: an unknown node 404, no Lean 503; a body that does not read 400. */
  def failed(e: Throwable): IO[Response[IO]] = e match
    case s: Stop           => IO.pure(Response[IO](s match
        case Stop.UnknownNode(_) => Status.NotFound
        case Stop.NoLean         => Status.ServiceUnavailable
        case _                   => Status.InternalServerError).withEntity(Json.obj("stop" -> s.asJson)))
    case m: MessageFailure => error(Status.BadRequest, m.getMessage)
    case other             => error(Status.InternalServerError, Option(other.getMessage).getOrElse(other.toString))
