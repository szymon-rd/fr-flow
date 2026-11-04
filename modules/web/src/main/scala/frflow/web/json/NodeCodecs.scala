package frflow.web.json

import frflow.api.node.*
import frflow.api.node.lean.*
import frflow.api.node.tests.*
import frflow.core.checking.{Assumed, Shown, Tested}
import frflow.core.example.Given
import frflow.core.expr.Mentions
import frflow.core.spec.NodeKind
import frflow.decision.review.{Cause, Mechanical, ReviewState, Standing, Unproven}
import frflow.eval.EvalError
import frflow.eval.run.Broken
import frflow.web.json.Leaves.given
import io.circe.Encoder
import io.circe.derivation.{Configuration, ConfiguredEncoder}

/** A node's view as the page reads it, group by group (`ViewCodecs` says the shape). */
object NodeCodecs:
  private given Configuration = Configuration.default.withDiscriminator("type")

  given Encoder.AsObject[NodeKind] = ConfiguredEncoder.derived
  given Encoder.AsObject[Mentions] = ConfiguredEncoder.derived
  given Encoder.AsObject[Relation] = ConfiguredEncoder.derived
  given Encoder.AsObject[Placement] = ConfiguredEncoder.derived
  given Encoder.AsObject[Says] = ConfiguredEncoder.derived
  given Encoder.AsObject[CheckState] = ConfiguredEncoder.derived
  given Encoder.AsObject[ObligationState] = ConfiguredEncoder.derived
  given Encoder.AsObject[Message] = ConfiguredEncoder.derived
  given Encoder.AsObject[ObligationView] = ConfiguredEncoder.derived
  given Encoder.AsObject[Forbidden] = ConfiguredEncoder.derived
  given Encoder.AsObject[TryView] = ConfiguredEncoder.derived
  given Encoder.AsObject[FindingView] = ConfiguredEncoder.derived
  given Encoder.AsObject[Unproven] = ConfiguredEncoder.derived
  given Encoder.AsObject[ProofView] = ConfiguredEncoder.derived
  given Encoder.AsObject[Tested] = ConfiguredEncoder.derived
  given Encoder.AsObject[Assumed] = ConfiguredEncoder.derived
  given Encoder.AsObject[Shown] = ConfiguredEncoder.derived
  given Encoder.AsObject[Cases] = ConfiguredEncoder.derived
  given Encoder.AsObject[Against] = ConfiguredEncoder.derived
  given Encoder.AsObject[EvalError] = ConfiguredEncoder.derived
  given Encoder.AsObject[Broken] = ConfiguredEncoder.derived
  given Encoder.AsObject[Given] = ConfiguredEncoder.derived
  given Encoder.AsObject[Drawn] = ConfiguredEncoder.derived
  given Encoder.AsObject[Step] = ConfiguredEncoder.derived
  given Encoder.AsObject[Ran] = ConfiguredEncoder.derived
  given Encoder.AsObject[Difference] = ConfiguredEncoder.derived
  given Encoder.AsObject[FailedCase] = ConfiguredEncoder.derived
  given Encoder.AsObject[TestOutcome] = ConfiguredEncoder.derived
  given Encoder.AsObject[Reach] = ConfiguredEncoder.derived
  given Encoder.AsObject[Target] = ConfiguredEncoder.derived
  given Encoder.AsObject[Note] = ConfiguredEncoder.derived
  given Encoder.AsObject[TestView] = ConfiguredEncoder.derived
  given Encoder.AsObject[CodeView] = ConfiguredEncoder.derived
  given Encoder.AsObject[ReviewState] = ConfiguredEncoder.derived
  given Encoder.AsObject[Cause] = ConfiguredEncoder.derived
  given Encoder.AsObject[Standing] = ConfiguredEncoder.derived
  given Encoder.AsObject[Mechanical.Not] = ConfiguredEncoder.derived
  given Encoder.AsObject[Decisions] = ConfiguredEncoder.derived
  given Encoder.AsObject[Movement] = ConfiguredEncoder.derived
  given Encoder.AsObject[ReviewView] = ConfiguredEncoder.derived
  given Encoder.AsObject[NodeView] = ConfiguredEncoder.derived
