package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*

/** The developer's review: the mechanical batch offered first, as one decision; then each node waiting,
  * in the order to decide it (parents and definitions first), shown as `show` shows it, then a prompt;
  * then the gone nodes. The queue is read again after each decision, so what it unblocked comes next.
  */
final class ReviewSession(api: FrFlowApi, term: Terminal, st: Style):
  private final case class Pass(skipped: Set[NodeId], batchOffered: Boolean, decided: Int):
    def skip(id: NodeId): Pass = copy(skipped = skipped + id)
    def recorded(n: Int): Pass = copy(decided = decided + n)

  def run(as: Option[String]): IO[ExitCode] =
    if !term.interactive then
      term.err("review is interactive: run it on a terminal (bin/frflow PROJECT review); without one, read inbox and decide with accept or reject --yes")
        .as(Run.Usage)
    else api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Run.Usage), dev => loop(dev, Pass(Set.empty, false, 0))))

  private def loop(dev: Developer, p: Pass): IO[ExitCode] = api.inbox.flatMap { inbox =>
    if !p.batchOffered && inbox.mechanical.nonEmpty then batch(dev, inbox, p)
    else inbox.queue.find(w => !p.skipped(w.node.id)) match
      case Some(w) => one(dev, w, inbox.queue.count(x => !p.skipped(x.node.id)), p)
      case None => inbox.gone.find(g => !p.skipped(g.id)).fold(finish(inbox, p))(gone(dev, _, p))
  }

  private def say(lines: List[String]) = term.out(lines)
  private def warn(line: String) = term.out(st.red(line))

  /** Asks until the answer is one of `keys` (the first letter counts); none at the end of the input. */
  private def choose(prompt: String, keys: Set[String]): IO[Option[String]] =
    term.read(prompt).flatMap {
      case None => IO.pure(None)
      case Some(a) =>
        val k = a.trim.toLowerCase.take(1)
        if keys(k) then IO.pure(Some(k)) else term.out(st.dim(s"one of: ${keys.toList.sorted.filter(_.nonEmpty).mkString(" ")}")) *> choose(prompt, keys)
    }

  private def reason(prompt: String): IO[Option[String]] = term.read(prompt).map(_.map(_.trim).filter(_.nonEmpty))

  /** Records `d`; a refusal is said, and the node skipped. */
  private def record(dev: Developer, d: Decide, p: Pass, node: Option[NodeId]): IO[ExitCode] =
    api.decide(d, dev).flatMap {
      case Left(r) => warn(s"refused: ${r.message}") *> loop(dev, node.fold(p)(p.skip))
      case Right(done) => say(st.green(s"recorded, signed by ${dev.name}:") :: ReportText.decided(done, st)) *> loop(dev, p.recorded(done.decisions.size))
    }

  private def batch(dev: Developer, inbox: Inbox, p: Pass): IO[ExitCode] =
    val ms = inbox.mechanical
    say("" :: st.heading(s"${ms.size} mechanical decision(s): Lean proves them again, and nothing in them is a choice") ::
      ms.map(r => "  " + Lines.node(r, st, 2))) *>
      choose("[a]ccept all, with one reason  [s]kip  [q]uit: ", Set("a", "s", "q")).flatMap {
        case Some("a") => reason("Why do they hold (e.g. a new field no rule reads)? ").flatMap {
          case Some(why) => record(dev, Decide.Confirm(why), p.copy(batchOffered = true), None)
          case None => loop(dev, p.copy(batchOffered = true))
        }
        case Some("s") => loop(dev, p.copy(batchOffered = true))
        case _ => finish(inbox, p)
      }

  private def one(dev: Developer, w: Queued, left: Int, p: Pass): IO[ExitCode] =
    val r = w.node
    val proposal = r.state == ReviewState.Proposed
    val keys = if proposal then "[a]ccept [r]eject [s]kip [q]uit [?]ask" else "[a]ccept [s]kip [q]uit [?]ask"
    api.details(r.id).flatMap { d =>
      say("" :: st.dim(s"${st.rule} $left waiting ${st.rule}") :: NodeText.lines(d, st) ++
        w.followers.map(f => st.dim(s"${st.follows} $f moved only with it: accepting ${r.id} confirms it"))) *>
        choose(s"\n$keys: ", Set("a", "r", "s", "q", "?", "").filter(k => proposal || k != "r")).flatMap {
          case Some("a") => accept(dev, r, p)
          case Some("r") => reason(s"Why not ${r.id}? ").flatMap(_.fold(loop(dev, p))(why =>
            record(dev, Decide.Reject(r.id, why, Some(r.review.version)), p, Some(r.id))))
          case Some("?") => term.read("What should change? ").flatMap {
            case Some(text) if text.trim.nonEmpty => api.ask(Some(r.id), text, dev).flatMap {
              case Left(e) => warn(s"refused: ${e.message}")
              case Right(q) => say(List(s"asked [${q.id}]: ${r.id} is with the agent until it answers or changes it"))
            } *> loop(dev, p.skip(r.id))
            case _ => loop(dev, p)
          }
          case Some("s") | Some("") => loop(dev, p.skip(r.id))
          case _ => api.inbox.flatMap(finish(_, p))
        }
    }

  /** Accepting: which decisions below to revisit (those that moved only with it are confirmed), why, then
    * what it records when that is more than the node itself.
    */
  private def accept(dev: Developer, r: Reviewed, p: Pass): IO[ExitCode] =
    val candidates = r.review.below.filter(_.kind == BelowKind.Accepted).map(_.id)
    val which =
      if candidates.isEmpty then IO.pure(Nil)
      else term.read(s"Revisit any decision below that this may affect (${candidates.mkString(" ")}; Enter for none)? ")
        .map(_.fold(Nil)(_.split("[\\s,]+").filter(_.nonEmpty).map(NodeId(_)).toList))
    which.flatMap { revisit =>
      reason(s"Why ${r.id}? ").flatMap {
        case None => loop(dev, p)
        case Some(why) =>
          val d = Decide.Accept(List(r.id), why, revisit, Map(r.id -> r.review.version))
          api.preview(d, dev).flatMap {
            case Left(e) => warn(s"refused: ${e.message}") *> loop(dev, p.skip(r.id))
            case Right(plan) if plan.decisions.size <= 1 => record(dev, d, p, Some(r.id))
            case Right(plan) =>
              say("This records:" :: ReportText.decided(plan, st)) *> choose("Record it? [y/n]: ", Set("y", "n")).flatMap {
                case Some("y") => record(dev, d, p, Some(r.id))
                case _ => loop(dev, p)
              }
          }
      }
    }

  private def gone(dev: Developer, g: Gone, p: Pass): IO[ExitCode] =
    say("" :: s"${st.bold(g.id.value)} ${st.red("is gone from the model")}: ${g.decision.content.statement}" ::
      st.dim(s"  last ${Words.verb(g.decision.action)} by ${g.decision.by}: ${g.decision.reason}") :: Nil) *>
      choose("[g]one: agree it is gone  [s]kip  [q]uit: ", Set("g", "s", "q", "")).flatMap {
        case Some("g") => reason(s"Why is ${g.id} gone? ").flatMap(_.fold(loop(dev, p))(why => record(dev, Decide.Gone(g.id, why), p, Some(g.id))))
        case Some("s") | Some("") => loop(dev, p.skip(g.id))
        case _ => api.inbox.flatMap(finish(_, p))
      }

  private def finish(inbox: Inbox, p: Pass): IO[ExitCode] =
    val left = inbox.queue.size + inbox.gone.size + inbox.mechanical.size
    say("" :: s"Decided ${p.decided} decision(s)${if left > 0 then s"; $left still waiting" else ""}." :: SummaryText.lines(inbox.overview, st))
      .as(ExitCode.Success)
