package frflow.web

import cats.effect.IO
import frflow.api.{Developer, Extension, Host}

/** What a layer on top adds to the web view: its routes (behind the page's token; under `/api/NAME/`, say), and a script
  * the page runs after its own, which registers with `FrFlow.extend({...})` (see the page).
  */
trait WebExtension extends Extension:
  def part(host: Host, dev: Developer): IO[WebPart]
