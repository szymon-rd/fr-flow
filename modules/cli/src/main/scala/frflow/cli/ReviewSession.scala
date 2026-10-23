package frflow.cli

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import frflow.api.*
import frflow.protocol.*

/** The developer's review: the mechanical batch, each node waiting in the order to decide it, then the gone nodes.
  * The view is read again after each decision, so what it unblocked comes next.
  */
final class ReviewSession(api: FrFlowApi, term: Terminal, st: Style):
  private final case class Pass(skipped: Set[NodeId], batchOffered: Boolean, decided: Int):
    def skip(id: NodeId): Pass = copy(skipped = skipped + id)
    def recorded(n: Int): Pass = copy(decided = decided + n)

  def run(as: Option[String]): IO[ExitCode] =
    if !term.interactive then
      term.err("review is interactive: run it on a terminal (bin/frflow PROJECT review); without one, read inbox and decide with accept or reject --yes")
        .as(Dispatch.Usage)
    else api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Dispatch.Usage), dev => loop(dev, Pass(Set.empty, false, 0))))

  private def loop(dev: Developer, p: Pass): IO[ExitCode] = api.reviewing.flatMap { (v, inbox) =>
    if !p.batchOffered && inbox.mechanical.nonEmpty then batch(dev, v, inbox, p)
    else inbox.queue.find(w => !p.skipped(w.node.id)) match
      case Some(w) => api.details(v, w.node).flatMap(one(dev, w, _, inbox.queue.count(x => !p.skipped(x.node.id)), p, Depth.Brief))
      case None => inbox.gone.find(g => !p.skipped(g.id)).fold(finish(inbox, p))(g => gone(dev, Details.gone(v, g), p))
  }

  private val Keys = Map("a" -> "[a]ccept", "r" -> "[r]eject", "s" -> "[s]kip", "v" -> "[v]iew", "q" -> "[q]uit", "?" -> "[?]ask")
  private def quit(p: Pass) = api.inbox.flatMap(finish(_, p))
  /** Until the answer is one of `keys` (its first letter counts); none at the end of the input. */
  private def choose(prompt: String, keys: Set[String]): IO[Option[String]] =
    term.read(prompt).flatMap {
      case None => IO.pure(None)
      case Some(a) =>
        val k = a.trim.toLowerCase.take(1)
        if keys(k) then IO.pure(Some(k)) else term.out(st.dim(s"one of: ${keys.toList.sorted.filter(_.nonEmpty).mkString(" ")}")) *> choose(prompt, keys)
    }
  private def reason(prompt: String): IO[Option[String]] = term.read(prompt).map(_.map(_.trim).filter(_.nonEmpty))

  // A refusal is said, and the node skipped.
  private def record(dev: Developer, d: Decide, p: Pass, node: Option[NodeId]): IO[ExitCode] =
    api.decide(d, dev).flatMap {
      case Left(r) => term.out(st.red(s"refused: ${r.message}")) *> loop(dev, node.fold(p)(p.skip))
      case Right(done) =>
        term.out(st.green(s"recorded, signed by ${dev.name}:") :: ReportText.decided(done, st, notes = false)) *> loop(dev, p.recorded(done.decisions.size))
    }

  // A mechanical decision is never of code (`Mechanical`): what changed is in its fields.
  private def batch(dev: Developer, v: View, inbox: Inbox, p: Pass): IO[ExitCode] =
    val ms = inbox.mechanical
    def lines(r: Reviewed, d: NodeDiff) =
      st.fit(s"  ${st.glyph(r)} ${st.bold(r.id.value)}  ${Lines.statement(r)}") :: DiffText.lines(d, st).drop(1).map(l => st.fit("  " + l))
    ms.traverse(r => api.diff(v, r).map(lines(r, _))).flatMap(changed =>
      term.out("" :: st.bold(s"${ms.size} mechanical decision(s): Lean proves them again, and nothing in them is a choice") :: changed.flatten)) *>
      choose("[a]ccept all, with one reason  [s]kip  [q]uit: ", Set("a", "s", "q")).flatMap {
        case Some("a") => reason("Why do they hold (e.g. a new field no rule reads)? ").flatMap {
          case Some(why) => record(dev, Decide.Confirm(why), p.copy(batchOffered = true), None)
          case None => loop(dev, p.copy(batchOffered = true))
        }
        case Some("s") => loop(dev, p.copy(batchOffered = true))
        case _ => finish(inbox, p)
      }

  private def one(dev: Developer, w: Queued, d: NodeDetails, left: Int, p: Pass, depth: Depth): IO[ExitCode] =
    val r = w.node
    val proposal = r.state == ReviewState.Proposed
    // One that waits for another is decided after it: its Decision section says which.
    val decides = if w.waitsFor.isDefined then Nil else if proposal then List("a", "r") else List("a")
    val keys = (decides ++ List("s", "v", "q", "?")).map(Keys).mkString(" ")
    term.out("" :: st.dim(s"${st.rule} $left waiting ${st.rule}") :: NodeText.lines(d, st, depth) ++
      w.followers.map(f => st.dim(Words.follower(f, r.id, st)))) *>
      choose(s"\n$keys: ", Set("s", "v", "q", "?", "") ++ decides).flatMap {
        case Some("a") => accept(dev, r, p)
        case Some("r") => reason(s"Why not ${r.id}? ").flatMap(_.fold(loop(dev, p))(why =>
          record(dev, Decide.Reject(r.id, why, Some(r.review.version)), p, Some(r.id))))
        case Some("v") => one(dev, w, d, left, p, Depth.Normal)
        case Some("?") => term.read("What should change? ").flatMap {
          case Some(text) if text.trim.nonEmpty => api.ask(Some(r.id), text, dev).flatMap {
            case Left(e) => term.out(st.red(s"refused: ${e.message}"))
            case Right(q) => term.out(List(s"asked [${q.id}]: ${r.id} is with the agent until it answers or changes it"))
          } *> loop(dev, p.skip(r.id))
          case _ => loop(dev, p)
        }
        case Some("s") | Some("") => loop(dev, p.skip(r.id))
        case _ => quit(p)
      }

  /** Asks which decisions below to revisit and why; shows what it records when that is more than the node. */
  private def accept(dev: Developer, r: Reviewed, p: Pass): IO[ExitCode] =
    val candidates = r.review.below.filter(_.kind == BelowKind.Accepted).map(_.id)
    // Asked again until each name is one of them; none at the end of the input.
    def which: IO[Option[List[NodeId]]] =
      if candidates.isEmpty then IO.pure(Some(Nil))
      else term.read(s"Revisit any decision below that this may affect (${candidates.mkString(" ")}; Enter for none)? ").flatMap {
        case None => IO.pure(None)
        case Some(a) =>
          val named = a.split("[\\s,]+").filter(_.nonEmpty).map(NodeId(_)).toList.distinct
          val other = named.filterNot(candidates.contains)
          if other.isEmpty then IO.pure(Some(named))
          else term.out(st.red(s"not a decision below ${r.id}: ${other.mkString(" ")}")) *> which
      }
    which.flatMap(_.fold(loop(dev, p)) { revisit =>
      reason(s"Why ${r.id}? ").flatMap {
        case None => loop(dev, p)
        case Some(why) =>
          val d = Decide.Accept(List(r.id), why, revisit, Map(r.id -> r.review.version))
          api.preview(d, dev).flatMap {
            case Left(e) => term.out(st.red(s"refused: ${e.message}")) *> loop(dev, p.skip(r.id))
            case Right(plan) if plan.decisions.size <= 1 && plan.unproven.isEmpty => record(dev, d, p, Some(r.id))
            case Right(plan) =>
              term.out("This records:" :: ReportText.decided(plan, st)) *> choose("Record it? [y/n]: ", Set("y", "n")).flatMap {
                case Some("y") => record(dev, d, p, Some(r.id))
                case _ => loop(dev, p)
              }
          }
      }
    })

  private def gone(dev: Developer, gn: GoneNode, p: Pass): IO[ExitCode] =
    val g = gn.gone
    term.out("" :: s"${st.bold(g.id.value)} ${st.red("is gone from the model")}: ${g.decision.content.statement}" ::
      st.dim(s"  last ${Words.verb(g.decision.action)} by ${g.decision.by}: ${g.decision.reason}") ::
      gn.renamedTo.map(y => st.yellow(s"  renamed to $y: it says the same")).toList) *>
      choose("[g]one: agree it is gone  [s]kip  [q]uit: ", Set("g", "s", "q", "")).flatMap {
        case Some("g") => reason(s"Why is ${g.id} gone? ").flatMap(_.fold(loop(dev, p))(why => record(dev, Decide.Gone(g.id, why), p, Some(g.id))))
        case Some("s") | Some("") => loop(dev, p.skip(g.id))
        case _ => quit(p)
      }

  private def finish(inbox: Inbox, p: Pass): IO[ExitCode] =
    term.out("" :: s"Decided ${p.decided} decision(s)." :: SummaryText.lines(inbox.overview, st)).as(ExitCode.Success)
