package frflow.cli.command

import cats.effect.{ExitCode, IO}
import frflow.api.FrFlowApi
import frflow.api.view.{Stop, Warning}
import frflow.cli.say.{Unprovens, Warnings}
import frflow.cli.review.Decisions
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.ReportText
import frflow.core.name.NodeId
import frflow.decision.ledger.Uncounted
import frflow.decision.rules.{Command as Decide, Refusal}

/** The deciding commands, as the developer types them: the reason given or asked for, who decides, what it records
  * shown and confirmed (or `--yes`); a node gone from the model is said so (rejecting it agrees it is gone); `rebase`
  * confirmed the same way.
  */
final class DecisionCommands(api: FrFlowApi[IO], term: Terminal, st: Style):
  private val decisions = Decisions(api, term, st)

  def decide(make: String => Decide, about: Option[NodeId], a: Asked): IO[ExitCode] =
    reason(a).flatMap {
      case None      => term.err("give the reason: --reason TEXT (it is kept as part of the theory)").as(Exit.Usage)
      case Some(why) => decisions.developer(a.as).flatMap(_.fold(IO.pure, by =>
          onGone(make(why), about).flatMap(_.fold(IO.pure, c =>
            decisions.take(c, by, _ => !a.yes).map(d => Exit.of(d.isDefined))))))
    }

  /** What the base accepts listed first (each decision taken out or changed against what was committed, and the
    * nodes it was of), `--yes` too; nothing to accept is refused.
    */
  def rebase(as: Option[String], yes: Boolean): IO[ExitCode] =
    decisions.developer(as).flatMap(_.fold(IO.pure, by => accepted.flatMap(ls =>
      if ls.isEmpty then decisions.refused(Refusal.NothingToRebase).as(Exit.Refused)
      else term.out(s"Rebasing accepts the ledger as it reads now, which no longer holds what was committed:" :: ls) >>
        rebased(yes, by))))

  /** Each decision that does not count because the committed history was rewritten, as a line. */
  private def accepted: IO[List[String]] = api.reading.view.map(_.warnings.collect {
    case Warning.NotCounted(id, d, why @ (Uncounted.Rewritten | Uncounted.Unreadable)) =>
      s"  ${st.bullet} ${Unprovens.verb(d.action)} $id by ${d.author.by} (${d.reason.text}): " +
        Warnings.uncounted(why, d)
  })

  private def rebased(yes: Boolean, by: String): IO[ExitCode] = confirmed(yes, by).flatMap {
      case Some(true)  => api.deciding.rebase(by).flatMap(_.fold(r => decisions.refused(r).as(Exit.Refused),
          r => term.out(ReportText.rebased(r)).as(Exit.Fine)))
      case Some(false) => term.out("Nothing written.").as(Exit.Refused)
      case None        => term.err("rebase is confirmed on a terminal; without one, pass --yes").as(Exit.Usage)
    }

  /** The reason given, else asked for on a terminal; none without one. */
  private def reason(a: Asked): IO[Option[String]] =
    def typed(r: Option[String]) = r.map(_.trim).filter(_.nonEmpty)
    if typed(a.reason).isDefined || !term.interactive then IO.pure(typed(a.reason))
    else term.read("Why (kept as part of the theory)? ").map(typed)

  /** A node gone from the model: rejecting it agrees it is gone (`Gone`); accepting or revisiting it is refused. A
    * name that is neither in the model nor gone from it is unknown (`Stop.UnknownNode`).
    */
  private def onGone(c: Decide, about: Option[NodeId]): IO[Either[ExitCode, Decide]] =
    api.reading.view.flatMap(v => about.filter(v.node(_).isEmpty) match
      case None                          => IO.pure(Right(c))
      case Some(id) if !v.gone.contains(id) => IO.raiseError(Stop.UnknownNode(id))
      case Some(id)                      => c match
        case Decide.Reject(_, why, _) => term.out(s"$id is gone from the model: recording that you agree it is gone")
            .as(Right(Decide.Gone(id, why)))
        case Decide.Gone(_, _)        => IO.pure(Right(c))
        case _                        => term.err(s"$id is gone from the model: it cannot be decided on (gone $id " +
            "-m REASON agrees it is gone)").as(Left(Exit.Refused)))

  private def confirmed(yes: Boolean, by: String): IO[Option[Boolean]] =
    if yes then IO.pure(Some(true))
    else if !term.interactive then IO.pure(None)
    else term.read(s"Accept the ledger as it reads now, as $by, as where its committed history starts? [y/N] ")
      .map(x => Some(x.exists(a => Set("y", "yes")(a.trim.toLowerCase))))
