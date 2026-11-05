package frflow.web

import cats.effect.IO
import frflow.api.{Extension, Host}

/** What a layer on top adds to the web view, for the project `host` opens and the developer deciding on the page: its
  * routes and script (`WebPart`). A layer proposes and asks; deciding stays the page's own routes.
  */
trait WebExtension extends Extension:
  def part(host: Host[IO], developer: String): IO[WebPart]
