package frflow.agent.command

import cats.effect.IO
import frflow.agent.work.AgentApi
import frflow.cli.review.ReviewKey

/** `[?]ask` in the review: instead of deciding a node, the developer asks the agent for a change; the node is with the
  * agent until it answers or changes it.
  */
object AskKey:
  def apply(api: IO[AgentApi[IO]]): ReviewKey = ReviewKey("?", "[?]ask", (dev, n, term, st) =>
    term.read("What should change? ").flatMap {
      case Some(text) if text.trim.nonEmpty => api.flatMap(_.ask(Some(n.id), text, dev)).flatMap {
          case Left(e)  => term.out(st.red(s"refused: ${e.message}"))
          case Right(q) => term.out(s"asked [${q.id.value}]: ${n.id} is with the agent until it answers or changes it")
        }
      case _                                => IO.unit
    })
