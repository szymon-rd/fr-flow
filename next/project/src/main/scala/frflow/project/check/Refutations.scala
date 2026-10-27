package frflow.project.check

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.core.spec.CallForms
import frflow.eval.Semantics
import frflow.project.pipeline.Analysis
import frflow.project.port.RunCode
import frflow.testing.{Case, Seed}
import frflow.testing.derive.Derive
import frflow.testing.search.{Refuted, StepRefutation}

/** The search for a case refuting a node's step, asked only once `complete` does not go through: among `Drawn`
  * cases of the node's inputs, drawn as its tests draw them, one on which the claim fails given the answer its one
  * part fixes (`StepRefutation`). It runs the developer's code, through `RunCode`.
  */
final class Refutations[F[_]](run: RunCode[F]):
  def of(a: Analysis, n: NodeId): F[Option[Refuted]] = run {
    val (r, e) = (a.decided, a.valid.elaborated)
    val draw = Derive.of(e, a.computed.examples.map(_._1))
    val one = r.theory.refinement.parts(n).size == 1
    r.theory.node(n).flatMap(_.statement.said).filter(_ => one).flatMap { f =>
      val types = CallForms.whole(f).value.params.map(_.ty)
      val seed = a.inputs.settings.seed
      val cases = (0 until Refutations.Drawn).toList.flatMap(i =>
        draw.values(types, Seed.sizeOf(i, Refutations.Drawn), seed.forCase(i)).map(Case(_, Nil)))
      Either.catchNonFatal(StepRefutation.candidate(Semantics(e), r, n, cases)).toOption.flatten
    }
  }

object Refutations:
  /** How many cases are drawn. */
  val Drawn: Int = 200
