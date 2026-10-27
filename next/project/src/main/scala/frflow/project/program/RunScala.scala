package frflow.project.program

import cats.effect.kernel.Sync
import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.consistency.Consistency
import frflow.core.example.Example
import frflow.core.name.NodeId
import frflow.core.spec.CallForms
import frflow.eval.{Races, Semantics}
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.project.pipeline.Computed
import frflow.proof.obligation.Constant
import frflow.testing.{Case, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.search.{Refuted, StepRefutation, Witnesses}

/** Running Scala before the pure phases (the developer's code runs, so `Sync`): each example against the code (a
  * throw said as one), the search for the witnesses of what must be shown possible (owner §18), from the values the
  * knowledge base's generators draw and small values, and, for each node with one part, a case refuting its step.
  * A value Lean is given holds no races' winners (Lean's `World` has no field for them).
  */
final class RunScala[F[_]: Sync](semantics: Semantics, draw: Derive):
  def apply(r: Resolved, examples: List[Example], settings: Settings): F[Computed] = Sync[F].blocking {
    val search = Witnesses(semantics, r.theory, draw.samples(_, settings.seed, RunScala.Drawn))
    Computed(examples.map(e => e -> onCode(r, e)),
      Consistency.vacuity(r.theory).flatMap(v => search.of(v).map(v -> _.map((x, ty) =>
        Constant(Races.without(x), ty)))).toMap,
      r.theory.nodes.map(_.node.id).flatMap(n => refuted(r, n, settings.seed).map(n -> _)).toMap)
  }

  private def onCode(r: Resolved, e: Example): OnCode =
    Either.catchNonFatal(ExampleRun(semantics, r.theory).of(e)).fold(t => OnCode.Threw(String.valueOf(t.getMessage)),
      identity)

  /** A case its step fails on, given the answer its one part allows, among cases of its inputs drawn as tests are. */
  private def refuted(r: Resolved, n: NodeId, seed: Seed): Option[Refuted] =
    val one = r.theory.refinement.parts(n).size == 1
    r.theory.node(n).flatMap(_.statement.said).filter(_ => one).flatMap { f =>
      val types = CallForms.whole(f).value.params.map(_.ty)
      val cases = (0 until RunScala.Drawn).toList.flatMap(i =>
        draw.values(types, Seed.sizeOf(i, RunScala.Drawn), seed.forCase(i)).map(Case(_, Nil)))
      Either.catchNonFatal(StepRefutation.candidate(semantics, r, n, cases)).toOption.flatten
    }

object RunScala:
  /** How many values are drawn for the witness search and the refutation search. */
  val Drawn: Int = 200
