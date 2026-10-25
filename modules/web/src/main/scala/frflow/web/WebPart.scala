package frflow.web

import cats.effect.IO
import org.http4s.HttpRoutes

final case class WebPart(routes: HttpRoutes[IO], script: String)
