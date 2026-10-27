package frflow.api.shell

import cats.effect.Async
import cats.syntax.all.*
import frflow.api.Deciding
import frflow.api.view.{Decided, Rebased}
import frflow.core.name.RelPath
import frflow.decision.rules.{Command, Refusal}
import frflow.project.pipeline.Analysis
import frflow.project.port.Records
import frflow.project.program.{DecideProgram, RebaseProgram, Decided as Recorded}
import frflow.wire.ledger.LedgerBaseFile

/** `Deciding` over a session: who decides, and `DecideProgram` on the subjects analysed now; an acceptance (`Accept`,
  * `Confirm`) on what this process checked and tested afresh (`Fresh`), never on the records on disk alone.
  */
private[api] final class Decides[F[_]: Async](s: Session[F], fresh: Fresh[F]) extends Deciding[F]:
  private val program = DecideProgram(s.ports)

  /** `as`, else `FRFLOW_AS`, else the name the key at hand is listed under in the committed deciders' list. */
  def developer(as: Option[String]): F[Either[Refusal, String]] = as.orElse(s.run.as) match
    case Some(name) => name.asRight[Refusal].pure[F]
    case None       => s.guarded((s.ports.keys.key, s.ports.keys.deciders).mapN((key, ds) =>
        ds.flatMap(_.entries.find(_.key == key)).map(_.name).toRight(Refusal.NoOneDecides)))

  def preview(c: Command, by: String): F[Either[Refusal, Decided]] =
    on(c).flatMap(a => s.guarded(program.preview(a.subjects, c, by))).map(_.map(view))

  def decide(c: Command, by: String): F[Either[Refusal, Decided]] =
    on(c).flatMap(a => s.guarded(program(a.subjects, c, by))).map(_.map(view))

  def rebase(by: String): F[Either[Refusal, Rebased]] =
    s.guarded(RebaseProgram(s.ports)(by)).map(_.map(b => Rebased(Decides.base, b.ledger)))

  private def on(c: Command): F[Analysis] = c match
    case Command.Accept(_, _, _, _) | Command.Confirm(_) => fresh.analysis
    case _                                               => s.analysis

  private def view(d: Recorded): Decided = Decided(d.recorded)

private[api] object Decides:
  val base: RelPath = Records.path(LedgerBaseFile.format)
