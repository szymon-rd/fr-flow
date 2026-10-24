package frflow.web

import cats.data.Kleisli
import cats.effect.IO
import cats.syntax.all.*
import frflow.api.*
import frflow.protocol.{Fingerprint, NodeId}
import io.circe.{Codec, Encoder, Json}
import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest
import org.http4s.{EntityEncoder, HttpApp, HttpRoutes, MediaType, MessageFailure, QueryParamDecoder, Response, Status, StaticFile, Request as Http}
import org.http4s.headers.`Content-Type`
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.dsl.io.*
import org.typelevel.ci.CIString

/** Who decides on the page, and whether the model's sources changed since `serve` started: then nothing is decided. */
final case class Serving(developer: String, modelChanged: Boolean) derives Codec.AsObject

/** One route per operation of the API, in its JSON, all behind the token `serve` printed. Decisions are `dev`'s, signed by
  * `api.decide` as the CLI's are; refused once the model's sources are no longer those this process compiled (`started`).
  * `layers`: what the layers on top add (their routes, behind the same token; their scripts, served as `/ext.js`).
  */
final class Routes(api: FrFlowApi, dev: Developer, token: String, started: Fingerprint, layers: List[WebPart] = Nil):
  import Routes.*

  // Only the browser opened from the printed link has the token: an agent's process on this machine does not.
  val app: HttpApp[IO] = Kleisli(req =>
    if !authorized(req) then error(Status.Forbidden, NoToken)
    else (routes <+> layers.map(_.routes).foldLeft(HttpRoutes.empty[IO])(_ <+> _))(req)
      .getOrElseF(error(Status.NotFound, s"no route ${req.method} ${req.uri.path}")).handleErrorWith(failed))

  private def authorized(req: Http[IO]): Boolean =
    req.headers.get(CIString(TokenHeader)).map(_.head.value).orElse(req.params.get("token"))
      .exists(t => MessageDigest.isEqual(t.getBytes(UTF_8), token.getBytes(UTF_8)))

  private def modelChanged: IO[Boolean] = api.modelFingerprint.map(_ != started)

  private val routes: HttpRoutes[IO] = HttpRoutes.of[IO] {
    case req @ GET -> Root => StaticFile.fromResource[IO]("/frflow/web/index.html", Some(req)).getOrElseF(error(Status.NotFound, "no page"))
    case GET -> Root / "api" / "serving" => modelChanged.flatMap(c => Ok(Serving(dev.name, c)))
    case GET -> Root / "api" / "view" => api.view.flatMap(Ok(_))
    case GET -> Root / "api" / "tree" :? From(from) => api.tree(from).flatMap(Ok(_))
    case GET -> Root / "api" / "details" / id => api.details(NodeId(id)).flatMap(Ok(_))
    case GET -> Root / "api" / "diff" / id => api.diff(NodeId(id)).flatMap(Ok(_))
    case GET -> Root / "api" / "inbox" => api.inbox().flatMap(Ok(_))
    case GET -> Root / "ext.js" =>
      // As text: the JSON encoder in scope here would quote it.
      IO.pure(Response[IO](Status.Ok).withEntity(layers.map(_.script).mkString("\n;\n"))(using EntityEncoder.stringEncoder[IO])
        .withContentType(`Content-Type`(MediaType.application.javascript)))
    case GET -> Root / "api" / "status" => api.status.flatMap(Ok(_))
    case GET -> Root / "api" / "find" :? Words(q) => api.view.flatMap(api.find(_, q)).flatMap(Ok(_))
    case req @ POST -> Root / "api" / "preview" => req.as[Decide].flatMap(api.preview(_, dev)).flatMap(answer)
    case req @ POST -> Root / "api" / "decide" =>
      req.as[Decide].flatMap(d => modelChanged.ifM(error(Status.Conflict, ModelChanged), api.decide(d, dev).flatMap(answer)))
    case POST -> Root / "api" / "check" :? From(node) => api.check(node).flatMap(Ok(_))
    case POST -> Root / "api" / "render" => api.render.flatMap(Ok(_))
  }

  private def answer[A: Encoder](r: Either[Refusal, A]): IO[Response[IO]] = r.fold(refused, Ok(_))

object Routes:
  val TokenHeader = "X-FrFlow-Token"
  val NoToken = "no session token: open the link `sbt \"PROJECT/serve\"` printed"
  val ModelChanged = "the model changed: restart serve (what is on disk is no longer what this server compiled)"

  private given QueryParamDecoder[NodeId] = QueryParamDecoder[String].map(NodeId(_))
  private object From extends OptionalQueryParamDecoderMatcher[NodeId]("node")
  private object Words extends QueryParamDecoderMatcher[String]("q")

  /** `{"error": message}`, the body of every failure. */
  def error(status: Status, message: String): IO[Response[IO]] =
    IO.pure(Response[IO](status).withEntity(Json.obj("error" -> Json.fromString(message))))

  private def refused(r: Refusal): IO[Response[IO]] = r match
    case Refusal.UnknownNode(_) => error(Status.NotFound, r.message)
    case _ => error(Status.Conflict, r.message)

  def failed(e: Throwable): IO[Response[IO]] = e match
    case FrFlowError.UnknownNode(_) => error(Status.NotFound, e.getMessage)
    case m: MessageFailure => error(Status.BadRequest, m.getMessage)
    case _ => error(Status.InternalServerError, Option(e.getMessage).getOrElse(e.toString))
