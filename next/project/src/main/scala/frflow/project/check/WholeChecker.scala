package frflow.project.check

import cats.data.NonEmptyList
import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.project.pipeline.Analysis
import frflow.project.port.Lake
import frflow.proof.layout.Layout
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation}
import frflow.proof.reading.Elaboration
import frflow.proof.verdict.{Judge, ObligationStatus, ProverRun, Result, WholeCheck}

/** The theory's own check: `Whole.lean` built and each consistency and vacuity obligation judged (proven when its
  * witnesses or FrFlow's automation meet it; one nothing witnesses stays open, "consistency not proven" or "not
  * shown"), then each example tried against the claims beside it (shown or not); a module Lake did not run judges
  * nothing. None when nothing is asked.
  */
final class WholeChecker[F[_]: Monad: Clock](lake: Lake[F]):
  def apply(a: Analysis): F[Option[WholeCheck]] =
    val layout = Layout(a.decided.theory.name)
    a.whole.toNel.traverse { asked =>
      (built(a, layout.whole), built(a, layout.wholeChecks), Clock[F].realTimeInstant).mapN((whole, checks, at) =>
        WholeCheck(a.keys.whole, asked.toList.map(o => judged(o, whole, checks)), at))
    }

  /** A module's run, with what Lean said of it; none when the model has no such module. */
  private def built(a: Analysis, name: ModuleName): F[Option[(ProverRun, Option[Elaboration])]] =
    a.modules.find(_.name == name).traverse(m => lake.build(NonEmptyList.one(name)).map(r => r -> Option.when(
      NodeLean.ran(name, r))(Elaboration(Print.module(m), NodeLean.output(r), m.name.file.value.stripPrefix("lean/")))))

  private def judged(o: Obligation, whole: Option[(ProverRun, Option[Elaboration])],
      checks: Option[(ProverRun, Option[Elaboration])]): Result =
    val (tried, in) = o.discharge match
      case Discharge.Attempt(_) => (true, checks)
      case _                    => (false, whole)
    in match
      case None                            => Result(o.name, ObligationStatus.Unchecked, Nil)
      case Some((ProverRun.TimedOut(_), _)) => Result(o.name, ObligationStatus.Timeout, Nil)
      case Some((_, None))                 => Result(o.name, if tried then ObligationStatus.NotShown
                                                else ObligationStatus.Unchecked, Nil)
      case Some((_, Some(e)))              => if tried then Judge.tried(o.name, e) else Judge.whole(o, e)
