package frflow.web

import cats.effect.IO
import cats.syntax.all.*
import com.comcast.ip4s.{Port, ipv4}
import frflow.api.{Developer, Extension, Host}
import org.http4s.HttpRoutes
import org.http4s.ember.server.EmberServerBuilder

/** What a layer on top adds to the web view: its routes (behind the page's token; under `/api/NAME/`, say), and a script
  * the page runs after its own, which registers with `FrFlow.extend({...})` (see the page).
  */
trait WebExtension extends Extension:
  def part(host: Host, dev: Developer): IO[WebPart]

final case class WebPart(routes: HttpRoutes[IO], script: String)

/** The web view: the page and the API's routes on localhost, in the project's own process (its model compiled once). */
object WebView:
  /** Serves until stopped, deciding as `dev`, with what the layers on top add; prints the link, which carries the token. */
  def serve(host: Host, dev: Developer, port: Int, layers: List[WebExtension] = Nil): IO[Unit] =
    val api = host.api
    for
      token <- newToken
      started <- api.modelFingerprint
      p <- IO.fromOption(Port.fromInt(port))(IllegalArgumentException(s"no port $port"))
      parts <- layers.traverse(_.part(host, dev))
      _ <- EmberServerBuilder.default[IO].withHost(ipv4"127.0.0.1").withPort(p).withHttpApp(Routes(api, dev, token, started, parts).app)
        .build.use(s => IO.println(s"FrFlow web view, deciding as ${dev.name}: http://127.0.0.1:${s.address.getPort}/?token=$token" +
          "\n(Ctrl-C stops it; after the model's sources change, start it again)") *> IO.never)
    yield ()

  private def newToken: IO[String] = IO {
    val b = new Array[Byte](18)
    java.security.SecureRandom().nextBytes(b)
    java.util.Base64.getUrlEncoder.withoutPadding.encodeToString(b)
  }
