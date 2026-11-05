package frflow.cli.review

import cats.effect.{ExitCode, IO}
import frflow.api.FrFlowApi
import frflow.api.view.{Decided, View}
import frflow.cli.say.Refusals
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.ReportText
import frflow.decision.rules.{Command as Decide, Refusal}

/** Taking a decision on the developer's word, as the command line and the review do: what it records shown and
  * confirmed on a terminal (unless `yes`), then recorded, signed; a refusal said with why. An acceptance is checked and
  * tested afresh first (the API does it: the records on disk are not trusted), which can take a while: it is said.
  */
final class Decisions(api: FrFlowApi[IO], term: Terminal, st: Style):
  /** Who decides: `as`, else `FRFLOW_AS`, else the name the key is listed under; none is a usage error, said. */
  def developer(as: Option[String]): IO[Either[ExitCode, String]] =
    api.deciding.developer(as).flatMap(_.fold(r => refused(r).as(Left(Exit.Usage)), d => IO.pure(Right(d))))

  /** `c` as `by`: previewed, then shown and confirmed when `ask` says of what it records; recorded once confirmed.
    * None: nothing recorded.
    */
  def take(c: Decide, by: String, ask: Decided => Boolean): IO[Option[Decided]] =
    afresh(c) >> api.deciding.preview(c, by).flatMap {
      case Left(r)  => refused(r).as(None)
      case Right(p) => confirmed(p, by, !ask(p)).flatMap {
        case Some(true)  => record(c, by)
        case Some(false) => term.out("Nothing recorded.").as(None)
        case None        => term.err("a decision is confirmed on a terminal; without one, pass --yes").as(None)
      }
    }

  /** Recorded without showing it first. */
  def record(c: Decide, by: String): IO[Option[Decided]] = api.deciding.decide(c, by).flatMap {
    case Left(r)     => refused(r).as(None)
    case Right(done) => term.out(s"Recorded, signed by $by:" :: ReportText.decided(done, st)).as(Some(done))
  }

  /** Said with why, on stderr; what moved under each node read from the view. */
  def refused(r: Refusal): IO[Unit] =
    api.reading.view.attempt.map(_.toOption).flatMap(v => term.err(s"refused: ${Refusals.text(r, causes(v))}"))

  private def causes(v: Option[View]) = (id: frflow.core.name.NodeId) =>
    v.flatMap(_.node(id)).fold(Nil)(_.review.standing.causes)

  /** None: no one can be asked. */
  private def confirmed(p: Decided, by: String, yes: Boolean): IO[Option[Boolean]] =
    if yes then IO.pure(Some(true))
    else if !term.interactive then IO.pure(None)
    else term.out(s"This records, as $by:" :: ReportText.decided(p, st)) >>
      term.read("Record it? [y/N] ").map(x => Some(x.exists(a => Set("y", "yes")(a.trim.toLowerCase))))

  private def afresh(c: Decide): IO[Unit] = c match
    case Decide.Accept(_, _, _, _) | Decide.Confirm(_) =>
      term.err(st.dim("checking and testing afresh before accepting (only what moved since this process last did)"))
    case _                                             => IO.unit
