package frflow.api.shell

import cats.effect.Async
import cats.syntax.all.*
import frflow.api.Deciding
import frflow.api.view.Decided
import frflow.decision.rules.{Command, Refusal}
import frflow.project.program.{DecideProgram, Decided as Recorded}

/** `Deciding` over a session: who decides, and `DecideProgram` on the subjects analysed now. */
private[api] final class Decides[F[_]: Async](s: Session[F]) extends Deciding[F]:
  private val program = DecideProgram(s.ports)

  /** `as`, else `FRFLOW_AS`, else the name the key at hand is listed under in the committed deciders' list. */
  def developer(as: Option[String]): F[Either[Refusal, String]] = as.orElse(s.run.as) match
    case Some(name) => name.asRight[Refusal].pure[F]
    case None       => s.guarded((s.ports.keys.key, s.ports.keys.deciders).mapN((key, ds) =>
        ds.flatMap(_.entries.find(_.key == key)).map(_.name).toRight(Refusal.NoOneDecides)))

  def preview(c: Command, by: String): F[Either[Refusal, Decided]] =
    s.analysis.flatMap(a => s.guarded(program.preview(a.subjects, c, by))).map(_.map(view))

  def decide(c: Command, by: String): F[Either[Refusal, Decided]] =
    s.analysis.flatMap(a => s.guarded(program(a.subjects, c, by))).map(_.map(view))

  private def view(d: Recorded): Decided = Decided(d.recorded)
