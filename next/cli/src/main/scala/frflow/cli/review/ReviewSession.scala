package frflow.cli.review

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import frflow.api.FrFlowApi
import frflow.api.node.NodeView
import frflow.api.view.View
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.{Contribution, DiffText, Depth, InboxText, Lines, NodeText, SummaryText}
import frflow.core.name.NodeId
import frflow.decision.review.ReviewState
import frflow.decision.rules.Command as Decide

/** The developer's review, on a terminal: the mechanical batch, each node waiting in the order to decide it, then the
  * decided nodes gone from the model. The view is read again after each decision, so what it unblocked comes next.
  * `added`: what layers on top add to a view (the nodes they hold back); `keys`: theirs to offer on a node.
  */
final class ReviewSession(api: FrFlowApi[IO], term: Terminal, st: Style, added: View => IO[Contribution],
    keys: List[ReviewKey]):
  private val ask = Prompts(term, st)
  private val decisions = Decisions(api, term, st)
  private val Own = Map("a" -> "[a]ccept", "r" -> "[r]eject", "s" -> "[s]kip", "v" -> "[v]iew", "q" -> "[q]uit")
  /** A layer's key does not take one of the review's own. */
  private val theirs = keys.filterNot(k => Own.contains(k.key) || k.key.isEmpty)

  def run(as: Option[String]): IO[ExitCode] =
    if !term.interactive then term.err("review is interactive: run it on a terminal; without one, read inbox and " +
      "decide with accept or reject --yes").as(Exit.Usage)
    else decisions.developer(as).flatMap(_.fold(IO.pure, loop(_, Pass.start)))

  /** The queue, then the gone nodes, then those a layer holds back (asked of the agent, say): shown last, never
    * dropped, to decide anyway or skip.
    */
  private def loop(dev: String, p: Pass): IO[ExitCode] = api.reading.view.flatMap(v => added(v).flatMap { x =>
    val queue = InboxText.queue(v, x.aside).filterNot(n => p.skipped(n.id))
    val held = InboxText.queue(v, Set.empty).filter(n => x.aside(n.id) && !p.skipped(n.id))
    def shown(n: NodeView, title: String)(d: Depth) = st.dim(s"${st.rule} $title ${st.rule}") ::
      NodeText(v, st, x).lines(n, d)
    if !p.batchOffered && queue.exists(InboxText.mechanical) then batch(dev, queue.filter(InboxText.mechanical), p)
    else queue.headOption match
      case Some(n) => one(dev, n, p, shown(n, s"${queue.size} waiting"))
      case None    => v.gone.find(g => !p.skipped(g)).fold(held.headOption.fold(finish(v, x, p))(n =>
          one(dev, n, p, shown(n, "held back by a layer (asked of the agent): decide it anyway, or skip"))))(
          gone(dev, _, p))
  })

  private def quit(p: Pass): IO[ExitCode] =
    api.reading.view.flatMap(v => added(v).flatMap(finish(v, _, p)))

  /** What a decision recorded counts; a refused one skips its node. */
  private def recorded(dev: String, p: Pass, node: Option[NodeId])(out: Option[frflow.api.view.Decided]) =
    loop(dev, out.fold(node.fold(p)(p.skip))(d => p.recorded(d.recorded.size)))

  private def batch(dev: String, ms: List[NodeView], p: Pass): IO[ExitCode] =
    val done = p.copy(batchOffered = true)
    val title = s"${ms.size} mechanical decision(s): Lean proves them again, and nothing in them is a choice"
    ms.flatTraverse(changed).flatMap(lines => term.out("" :: st.bold(title) :: lines)) >>
      ask.choose("[a]ccept all, with one reason  [s]kip  [q]uit: ", Set("a", "s", "q")).flatMap {
        case Some("a") => ask.reason("Why do they hold (e.g. a new field no rule reads)? ").flatMap(_.fold(
            loop(dev, done))(why => decisions.take(Decide.Confirm(why), dev, _ => false).flatMap(recorded(dev, done,
            None))))
        case Some("s") => loop(dev, done)
        case _         => quit(p)
      }

  /** A node in a line, and what moved in its fields. */
  private def changed(n: NodeView): IO[List[String]] = api.reading.diff(n.id).map(d =>
    Lines.node(n, st, 2) :: d.toList.flatMap(_.fields.flatMap(DiffText.field(_, st))).map("    " + _))

  /** `shown`: the node as printed at a depth (`Brief` here, `Normal` once viewed). */
  private def one(dev: String, n: NodeView, p: Pass, shown: Depth => List[String]): IO[ExitCode] =
    val proposal = n.review.standing.state == ReviewState.Proposed
    // One that waits for another is decided after it: its Decision section says which.
    val decides = if n.review.waitsFor.isDefined then Nil else if proposal then List("a", "r") else List("a")
    val offered = ((decides ++ List("s", "v", "q")).map(Own) ++ theirs.map(_.label)).mkString(" ")
    term.out("" :: shown(Depth.Brief)) >>
      ask.choose(s"\n$offered: ", Set("s", "v", "q", "") ++ decides ++ theirs.map(_.key)).flatMap {
        case Some("a")          => accept(dev, n, p)
        case Some("r")          => ask.reason(s"Why not ${n.id}? ").flatMap(_.fold(loop(dev, p))(why =>
            decisions.take(Decide.Reject(n.id, why, Some(n.review.version)), dev, _ => false)
              .flatMap(recorded(dev, p, Some(n.id)))))
        case Some("v")          => one(dev, n, p, _ => shown(Depth.Normal))
        case Some("s") | Some("") => loop(dev, p.skip(n.id))
        case Some(k) if theirs.exists(_.key == k) =>
          theirs.find(_.key == k).fold(IO.unit)(_.act(dev, n, term, st)) >> loop(dev, p.skip(n.id))
        case _                  => quit(p)
      }

  /** Which decisions below to revisit, and why; what it records shown first when that is more than the node. */
  private def accept(dev: String, n: NodeView, p: Pass): IO[ExitCode] =
    ask.revisit(n.id, n.review.moves.below).flatMap(_.fold(loop(dev, p))(revisit =>
      ask.reason(s"Why ${n.id}? ").flatMap(_.fold(loop(dev, p)) { why =>
        val c = Decide.Accept(List(n.id), why, revisit, Map(n.id -> n.review.version))
        decisions.take(c, dev, _.recorded.size > 1).flatMap(recorded(dev, p, Some(n.id)))
      })))

  private def gone(dev: String, id: NodeId, p: Pass): IO[ExitCode] =
    term.out(List("", s"${st.bold(id.value)} ${st.red("is gone from the model")}: it was decided, and the model no " +
      "longer has it")) >> ask.choose("[g]one: agree it is gone  [s]kip  [q]uit: ", Set("g", "s", "q", "")).flatMap {
      case Some("g")            => ask.reason(s"Why is $id gone? ").flatMap(_.fold(loop(dev, p))(why =>
          decisions.take(Decide.Gone(id, why), dev, _ => false).flatMap(recorded(dev, p, Some(id)))))
      case Some("s") | Some("") => loop(dev, p.skip(id))
      case _                    => quit(p)
    }

  private def finish(v: View, x: Contribution, p: Pass): IO[ExitCode] =
    term.out("" :: s"Decided ${p.decided} decision(s)." ::
      SummaryText.lines(v, InboxText.waiting(v, x.aside), st, x.waiting)).as(Exit.Fine)
