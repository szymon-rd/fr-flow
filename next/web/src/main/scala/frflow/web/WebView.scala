package frflow.web

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import com.comcast.ip4s.{Port, ipv4}
import frflow.api.Host
import java.net.URI
import org.http4s.ember.server.EmberServerBuilder

/** The web view: the page and the API's routes on localhost, in the project's own process (its model compiled once),
  * deciding as `developer`, with what the layers on top add. Held while the resource is: its link carries the
  * session's token.
  */
object WebView:
  /** How long a stop waits for open connections (a browser keeps one alive). */
  private val Stopping = scala.concurrent.duration.FiniteDuration(1, "second")

  /** The server on `port` (0: any free one), and its link. */
  def server(host: Host[IO], developer: String, port: Int, layers: List[WebExtension]): Resource[IO, URI] =
    for
      token   <- Resource.eval(newToken)
      started <- Resource.eval(host.api.reading.modelFingerprint)
      p       <- Resource.eval(IO.fromOption(Port.fromInt(port))(IllegalArgumentException(s"no port $port")))
      parts   <- Resource.eval(layers.traverse(_.part(host, developer)))
      s       <- EmberServerBuilder.default[IO].withHost(ipv4"127.0.0.1").withPort(p).withShutdownTimeout(Stopping)
                   .withHttpApp(Routes(host.api, developer, Gate(token, started), parts).app).build
    yield URI(s"http://127.0.0.1:${s.address.getPort}/?token=$token")

  /** Serves until stopped, the link printed. */
  def serve(host: Host[IO], developer: String, port: Int, layers: List[WebExtension]): IO[Unit] =
    server(host, developer, port, layers).use(link => IO.println(s"FrFlow web view, deciding as $developer: $link\n" +
      "(Ctrl-C stops it; after the model's sources change, start it again)") >> IO.never)

  private def newToken: IO[String] = IO {
    val b = new Array[Byte](18)
    java.security.SecureRandom().nextBytes(b)
    java.util.Base64.getUrlEncoder.withoutPadding.encodeToString(b)
  }
