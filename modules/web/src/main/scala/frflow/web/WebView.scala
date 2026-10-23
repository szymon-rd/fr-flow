package frflow.web

import cats.effect.IO
import com.comcast.ip4s.{Port, ipv4}
import frflow.api.{Developer, FrFlowApi}
import org.http4s.ember.server.EmberServerBuilder

/** The web view: the page and the API's routes on localhost, in the project's own process (its model compiled once). */
object WebView:
  /** Serves until stopped, deciding as `dev`; prints the link, which carries the token. */
  def serve(api: FrFlowApi, dev: Developer, port: Int): IO[Unit] =
    for
      token <- newToken
      started <- api.modelFingerprint
      p <- IO.fromOption(Port.fromInt(port))(IllegalArgumentException(s"no port $port"))
      _ <- EmberServerBuilder.default[IO].withHost(ipv4"127.0.0.1").withPort(p).withHttpApp(Routes(api, dev, token, started).app)
        .build.use(s => IO.println(s"FrFlow web view, deciding as ${dev.name}: http://127.0.0.1:${s.address.getPort}/?token=$token" +
          "\n(Ctrl-C stops it; after the model's sources change, start it again)") *> IO.never)
    yield ()

  private def newToken: IO[String] = IO {
    val b = new Array[Byte](18)
    java.security.SecureRandom().nextBytes(b)
    java.util.Base64.getUrlEncoder.withoutPadding.encodeToString(b)
  }
