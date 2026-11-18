package frflow.web

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import com.comcast.ip4s.{Port, ipv4}
import frflow.api.{FrFlowApi, Host}
import java.net.URI
import org.http4s.ember.server.EmberServerBuilder

/** The web view: the page and the API's routes on localhost, in the project's own process (its model compiled once),
  * deciding as `developer`, with what the layers on top add. Held while the resource is: its link carries the
  * session's token, a new one each start unless the environment gives it (`FRFLOW_WEB_TOKEN`: a supervisor starting
  * the server again on a rebuilt model keeps the page's link working).
  */
object WebView:
  /** How long a stop waits for open connections (a browser keeps one alive). */
  private val Stopping = scala.concurrent.duration.FiniteDuration(1, "second")

  /** The server on `port` (0: any free one), and its link. */
  def server(api: FrFlowApi[IO], host: Host[IO], developer: String, port: Int)(layers: List[WebExtension])
      : Resource[IO, URI] =
    for
      token   <- Resource.eval(host.env.get(WebView.TokenVariable).filter(_.nonEmpty).fold(newToken)(IO.pure))
      started <- Resource.eval(api.reading.modelFingerprint)
      live    <- Resource.eval(newToken.map(Live.of(_, host.directory, host.env)))
      p       <- Resource.eval(IO.fromOption(Port.fromInt(port))(IllegalArgumentException(s"no port $port")))
      parts   <- Resource.eval(layers.traverse(_.part(host, developer)))
      s       <- EmberServerBuilder.default[IO].withHost(ipv4"127.0.0.1").withPort(p).withShutdownTimeout(Stopping)
                   .withHttpApp(Routes(api, developer, Gate(token, started), live, parts).app).build
    yield URI(s"http://127.0.0.1:${s.address.getPort}/?token=$token")

  /** Serves until stopped, the link printed. */
  def serve(api: FrFlowApi[IO], host: Host[IO], developer: String, port: Int)(layers: List[WebExtension]): IO[Unit] =
    server(api, host, developer, port)(layers).use(link =>
      IO.println(s"FrFlow web view, deciding as $developer: $link\n" + (if Live.of("", host.directory, host.env).reloads
        then "(started again on the rebuilt model whenever its sources change)"
        else "(Ctrl-C stops it; after the model's sources change, start it again, or use bin/frflow-web)")) >> IO.never)

  /** The environment variable that fixes the session's token. */
  val TokenVariable = "FRFLOW_WEB_TOKEN"

  private def newToken: IO[String] = IO {
    val b = new Array[Byte](18)
    java.security.SecureRandom().nextBytes(b)
    java.util.Base64.getUrlEncoder.withoutPadding.encodeToString(b)
  }
