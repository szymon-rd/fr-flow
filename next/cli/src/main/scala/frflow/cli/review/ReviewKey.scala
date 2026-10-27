package frflow.cli.review

import cats.effect.IO
import frflow.api.node.NodeView
import frflow.cli.term.{Style, Terminal}

/** A key a layer on top offers on a node in the review (`?` to ask the agent, say): `act` runs on it as the developer
  * named, and the review moves on to the next node. It never decides: deciding is the review's own keys.
  */
final case class ReviewKey(key: String, label: String, act: (String, NodeView, Terminal, Style) => IO[Unit])
