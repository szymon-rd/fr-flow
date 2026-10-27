package frflow.web

import cats.effect.IO
import org.http4s.HttpRoutes

/** What a layer on top adds to the page: its routes (behind the page's token; under `/api/NAME/`, say), and a script
  * the page runs after its own, which registers with `FrFlow.extend({...})`.
  */
final case class WebPart(routes: HttpRoutes[IO], script: String)
