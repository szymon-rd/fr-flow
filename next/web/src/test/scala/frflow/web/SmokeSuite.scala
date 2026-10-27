package frflow.web

import cats.effect.IO
import frflow.api.{Host, Opened}
import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.nio.file.Path

/** The web view served for real: started on a free port of localhost, the page and one API route fetched over
  * HTTP with the link's token, then stopped.
  */
class SmokeSuite extends munit.CatsEffectSuite:
  private val client = HttpClient.newBuilder().version(HttpClient.Version.HTTP_1_1).build()
  private def fetch(uri: URI): IO[HttpResponse[String]] =
    IO.blocking(client.send(HttpRequest.newBuilder(uri).GET().build(), HttpResponse.BodyHandlers.ofString()))

  test("the server starts on a free port, serves the page and the view with the token, and stops") {
    Opened.api(Opened.before).flatMap { api =>
      val host = Host(api, Path.of(".").toAbsolutePath, Map.empty)
      WebView.server(host, "ann", 0, Nil).use { link =>
        val root = URI(s"${link.getScheme}://${link.getAuthority}")
        for
          page   <- fetch(link)
          view   <- fetch(root.resolve(s"/api/view?${link.getQuery}"))
          denied <- fetch(root.resolve("/api/view"))
        yield
          assertEquals(page.statusCode, 200)
          assert(page.body.contains("<title>FrFlow</title>"), page.body.take(200))
          assertEquals(view.statusCode, 200)
          assert(view.body.contains("\"id\":\"nonNegative\""), view.body.take(300))
          assertEquals(denied.statusCode, 403)
          root
      }.flatMap(root => fetch(root.resolve("/")).attempt.map(r => assert(r.isLeft, r)))
    }
  }
