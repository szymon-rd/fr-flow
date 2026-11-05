package frflow.web

import cats.effect.IO
import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest
import org.http4s.{MediaType, Method, Request, Status}
import org.typelevel.ci.CIString

/** What a request passes through: the session's token (only the browser opened from the printed link has it, not an
  * agent's process on this machine), and the model's fingerprint when `serve` started (deciding is refused once it
  * moves: what is on disk is no longer what this process compiled).
  */
final case class Gate(token: String, started: String):
  def admits(offered: Option[String]): Boolean =
    offered.exists(t => MessageDigest.isEqual(t.getBytes(UTF_8), token.getBytes(UTF_8)))

  /** Why `req` is turned away, if it is: without the token (in its header; in the link only for the page and its
    * scripts, which a browser loads without headers), from another page's origin, or a write whose body is not JSON
    * (a form another page posts).
    */
  def refuses(req: Request[IO]): Option[(Status, String)] =
    if !admits(offered(req)) then Some(Status.Forbidden -> Routes.NoToken)
    else if foreign(req) then Some(Status.Forbidden -> Gate.Foreign)
    else if req.method != Method.GET && !req.contentType.exists(_.mediaType == MediaType.application.json) then
      Some(Status.UnsupportedMediaType -> Gate.NotJson)
    else None

  private def offered(req: Request[IO]): Option[String] =
    header(req, Routes.TokenHeader).orElse(req.params.get("token")
      .filter(_ => req.method == Method.GET && Gate.Linked(req.uri.path.renderString)))

  /** An `Origin` that is not this server's own (`http://` and the `Host` the browser asked for). */
  private def foreign(req: Request[IO]): Boolean =
    header(req, "Origin").exists(o => !header(req, "Host").exists(h => o == s"http://$h"))

  private def header(req: Request[IO], name: String): Option[String] =
    req.headers.get(CIString(name)).map(_.head.value)

object Gate:
  /** The paths a link may carry the token to: the page, and the layers' scripts it loads. */
  val Linked: Set[String] = Set("/", "/ext.js")
  val Foreign = "another page's origin: only the page this server serves may call it"
  val NotJson = "a write takes a JSON body (Content-Type: application/json)"
