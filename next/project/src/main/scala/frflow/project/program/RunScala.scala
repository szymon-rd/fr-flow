package frflow.project.program

import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.consistency.Consistency
import frflow.core.example.Example
import frflow.eval.{Races, Semantics}
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.project.pipeline.Computed
import frflow.project.port.RunCode
import frflow.proof.obligation.Constant
import frflow.testing.Settings
import frflow.testing.derive.Derive
import frflow.testing.search.Witnesses

/** Running Scala before the pure phases (the developer's code runs, through `RunCode`): each example against the
  * code (a throw said as one), and the search for the witnesses of what must be shown possible (owner §18), from the
  * values the FrModel's generators draw and small values. A value Lean is given holds no races' winners
  * (Lean's `World` has no field for them).
  */
final class RunScala[F[_]](run: RunCode[F], semantics: Semantics, draw: Derive):
  def apply(r: Resolved, examples: List[Example], settings: Settings): F[Computed] = run {
    val search = Witnesses(semantics, r.theory, draw.samples(_, settings.seed, RunScala.Drawn))
    Computed(examples.map(e => e -> onCode(r, e)),
      Consistency.vacuity(r.theory).flatMap(v => search.of(v).map(v -> _.map((x, ty) =>
        Constant(Races.without(x), ty)))).toMap)
  }

  private def onCode(r: Resolved, e: Example): OnCode =
    Either.catchNonFatal(ExampleRun(semantics, r.theory).of(e)).fold(t => OnCode.Threw(String.valueOf(t.getMessage)),
      identity)

object RunScala:
  /** How many values of each type are drawn for the witness search. */
  val Drawn: Int = 200
