package frflow.agent.command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import frflow.agent.request.Request
import frflow.agent.work.{AgentApi, Moved}
import frflow.core.name.NodeId
import frflow.decision.ledger.Decision
import frflow.api.Host
import frflow.cli.term.{Exit, Style, Terminal}
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** `wait`: the agent's hook on the developer. It blocks until the developer decides a node or asks for something,
  * then prints what moved and ends; an agent runs it in the background and is woken when it ends. It watches the
  * files a decision or a request writes (`.frflow/ledger.json`, `.frflow/requests.json`) and reads the decisions and
  * the requests again only when one changes: never the model, which may have changed since this process compiled it.
  */
object Waiting:
  private val Tick = 1.second

  /** The project as the agent reads it: the layer's API over it, and the project. */
  final case class Watched(agent: AgentApi[IO], host: Host[IO]):
    /** The decisions as the ledger holds them, and the requests. */
    def read: IO[(Map[NodeId, List[Decision]], List[Request])] = (host.reading.decisions, agent.requests).tupled

  def run(w: Watched, term: Terminal, st: Style, limit: FiniteDuration): IO[ExitCode] =
    for
      before <- w.read
      files  <- watched(w.host.directory)
      moved  <- until(w, before, files, limit)
      code   <- moved.fold(term.out(List(s"nothing decided or asked in ${limit.toMinutes} min; wait again"))
                  .as(Exit.Fine))(ms => term.out(ms.map(line(_, st)) :+ st.dim("inbox: the rest")).as(Exit.Fine))
    yield code

  /** What moved from `before`, once a watched file changes and something did; none if `left` runs out first. */
  private def until(w: Watched, before: (Map[NodeId, List[Decision]], List[Request]), files: String,
      left: FiniteDuration): IO[Option[List[Moved]]] =
    if left <= Duration.Zero then IO.pure(None)
    else IO.sleep(Tick) >> watched(w.host.directory).flatMap(now =>
      if now == files then until(w, before, files, left - Tick)
      else w.read.map(Moved.between(before, _)).flatMap(ms =>
        if ms.nonEmpty then IO.pure(Some(ms)) else until(w, before, now, left - Tick)))

  /** The texts of the files a decision or a request writes. */
  private def watched(dir: Path): IO[String] = IO.blocking(
    List(dir.resolve(".frflow/ledger.json"), AgentApi.requestsFile(dir))
      .map(p => if Files.exists(p) then Files.readString(p) else "").mkString("\u0000"))

  private def line(m: Moved, st: Style): String = m match
    case Moved.Accepted(n, by)        => s"${st.bold(n.value)}: ${st.green(s"accepted by $by")}"
    case Moved.Rejected(n, by, why)   => s"${st.bold(n.value)}: ${st.red(s"rejected by $by")}: ${why.trim}; " +
        "propose what the reason asks for in its place"
    case Moved.Revisit(n, by, why)    => s"${st.bold(n.value)}: ${st.yellow(s"$by asked to revisit it")}: ${why.trim}"
    case Moved.Gone(n, by)            => s"${st.bold(n.value)}: $by agreed it is gone"
    case Moved.Asked(q)               => s"[${q.id.value}] ${st.magenta(s"${q.asked.by} asks")} on " +
        s"${q.node.fold("the idea")(_.value)}: ${q.text}"
