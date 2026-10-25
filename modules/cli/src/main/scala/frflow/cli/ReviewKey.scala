package frflow.cli

import cats.effect.IO
import frflow.api.Developer
import frflow.protocol.Reviewed

/** A key the review offers on a node: `act` runs on it, and the review moves on to the next. */
final case class ReviewKey(key: String, label: String, act: (Developer, Reviewed, Terminal, Style) => IO[Unit])
