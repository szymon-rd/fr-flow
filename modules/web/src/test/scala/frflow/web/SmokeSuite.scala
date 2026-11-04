package frflow.web

import cats.effect.IO
import frflow.api.{Host, Opened}
import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.nio.file.Path

/** The web view served for real: started on a free port of localhost, the page fetched with the link's token, the
  * view with the token's header, a write from its own origin and from another, then stopped.
  */
class SmokeSuite extends munit.CatsEffectSuite:
  private val client = HttpClient.newBuilder().version(HttpClient.Version.HTTP_1_1).build()
  private def fetch(uri: URI): IO[HttpResponse[String]] = sent(HttpRequest.newBuilder(uri).GET().build())
  private def sent(r: HttpRequest): IO[HttpResponse[String]] =
    IO.blocking(client.send(r, HttpResponse.BodyHandlers.ofString()))
  private val accept =
    """{"action": "accept", "nodes": ["nonNegative"], "reason": "it says what the service must do"}"""

  /** A preview posted as the page posts it, from `origin`. */
  private def preview(root: URI, token: String, origin: URI): IO[HttpResponse[String]] = sent(HttpRequest.newBuilder(
    root.resolve("/api/preview")).header(Routes.TokenHeader, token).header("Content-Type", "application/json")
    .header("Origin", origin.toString).POST(HttpRequest.BodyPublishers.ofString(accept)).build())

  test("the server starts on a free port, serves the page and the view with the token, and stops") {
    Opened.api(Opened.before).flatMap { api =>
      val host = Host.of(api, Path.of(".").toAbsolutePath, Map.empty)
      WebView.server(api, host, "ann", 0)(Nil).use { link =>
        val root = URI(s"${link.getScheme}://${link.getAuthority}")
        for
          page   <- fetch(link)
          token   = link.getQuery.stripPrefix("token=")
          view   <- sent(HttpRequest.newBuilder(root.resolve("/api/view")).header(Routes.TokenHeader, token).build())
          denied <- fetch(root.resolve(s"/api/view?${link.getQuery}"))
          own    <- preview(root, token, root)
          evil   <- preview(root, token, URI("http://evil.example"))
        yield
          assertEquals(page.statusCode, 200)
          assert(page.body.contains("<title>FrFlow</title>"), page.body.take(200))
          assertEquals(view.statusCode, 200)
          assert(view.body.contains("\"id\":\"nonNegative\""), view.body.take(300))
          assertEquals((denied.statusCode, own.statusCode, evil.statusCode), (403, 200, 403))
          assertEquals(page.headers.firstValue("Referrer-Policy").orElse(""), "no-referrer")
          root
      }.flatMap(root => fetch(root.resolve("/")).attempt.map(r => assert(r.isLeft, r)))
    }
  }
