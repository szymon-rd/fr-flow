package frflow.web.json

import cats.syntax.all.*
import frflow.api.view.*
import frflow.api.view.diff.*
import frflow.api.view.source.*
import frflow.api.view.vocab.*
import frflow.core.ty.Field
import frflow.core.vocab.{SymbolType, ValueKind}
import frflow.api.view.whole.*
import frflow.core.analysis.Problem
import frflow.core.consistency.{Picked, Vacuity, Witness}
import frflow.decision.ledger.Uncounted
import frflow.decision.rules.Refusal
import frflow.eval.run.OnCode
import frflow.web.json.Leaves.given
import frflow.web.json.NodeCodecs.given
import io.circe.derivation.{Configuration, ConfiguredEncoder}
import io.circe.syntax.*
import io.circe.{Encoder, Json, JsonObject}
import frflow.core.analysis.outside.Premise

/** The views as the page reads them: each record an object of its fields, each case of an enum an object naming it
  * (`{"type": "Ungoverned", "file": …}`), the leaves as `Leaves` writes them; an example with whether it passes, and
  * what a decision recorded as each node with its decision.
  */
object ViewCodecs:
  private given Configuration = Configuration.default.withDiscriminator("type")

  given Encoder.AsObject[Picked] = ConfiguredEncoder.derived
  given Encoder.AsObject[Witness] = ConfiguredEncoder.derived
  given Encoder.AsObject[GroupStatus] = ConfiguredEncoder.derived
  given Encoder.AsObject[GroupView] = ConfiguredEncoder.derived
  given Encoder.AsObject[Vacuity] = ConfiguredEncoder.derived
  given Encoder.AsObject[OnCode] = ConfiguredEncoder.derived
  given Encoder.AsObject[OnClaims] = ConfiguredEncoder.derived
  given Encoder.AsObject[ExampleOutcome] = ConfiguredEncoder.derived
  given Encoder.AsObject[ExampleView] = Encoder.AsObject.instance(e =>
    ConfiguredEncoder.derived[ExampleView].encodeObject(e).add("outcome", e.outcome.asJson))
  given Encoder.AsObject[WholeView] = ConfiguredEncoder.derived
  given Encoder.AsObject[Piece] = ConfiguredEncoder.derived
  given Encoder.AsObject[Overview] = ConfiguredEncoder.derived
  given Encoder.AsObject[Uncounted] = ConfiguredEncoder.derived
  given Encoder.AsObject[NotMade] = ConfiguredEncoder.derived
  given Encoder.AsObject[Warning] = ConfiguredEncoder.derived
  given Encoder.AsObject[SystemView] = ConfiguredEncoder.derived
  given Encoder.AsObject[View] = ConfiguredEncoder.derived
  given Encoder.AsObject[DiffLine] = ConfiguredEncoder.derived
  given Encoder.AsObject[FieldDiff] = ConfiguredEncoder.derived
  given Encoder.AsObject[Moved] = ConfiguredEncoder.derived
  given Encoder.AsObject[Parts] = ConfiguredEncoder.derived
  given Encoder.AsObject[NodeDiff] = ConfiguredEncoder.derived
  given Encoder.AsObject[Found] = ConfiguredEncoder.derived
  given Encoder.AsObject[MeantBy] = ConfiguredEncoder.derived
  given Encoder.AsObject[Meaning] = ConfiguredEncoder.derived
  given Encoder.AsObject[FilePart] = ConfiguredEncoder.derived
  given Encoder.AsObject[SourceFile] = ConfiguredEncoder.derived
  given Encoder.AsObject[RocqText] = ConfiguredEncoder.derived
  given Encoder.AsObject[Sources] = ConfiguredEncoder.derived
  given Encoder.AsObject[CheckEvent] = ConfiguredEncoder.derived
  given Encoder[ValueKind] = Encoder.encodeString.contramap(_.toString)
  given Encoder.AsObject[SymbolType] = ConfiguredEncoder.derived
  given Encoder.AsObject[Field] = ConfiguredEncoder.derived
  given Encoder.AsObject[Word] = ConfiguredEncoder.derived
  given Encoder.AsObject[Defined] = ConfiguredEncoder.derived
  given Encoder.AsObject[Case] = ConfiguredEncoder.derived
  given Encoder.AsObject[Shape] = ConfiguredEncoder.derived
  given Encoder.AsObject[DomainType] = ConfiguredEncoder.derived
  given Encoder.AsObject[Vocab] = ConfiguredEncoder.derived
  given Encoder.AsObject[Scaffolded] = ConfiguredEncoder.derived
  given Encoder.AsObject[Rebased] = ConfiguredEncoder.derived
  given Encoder.AsObject[Refusal] = ConfiguredEncoder.derived
  given Encoder.AsObject[Problem.Place] = ConfiguredEncoder.derived
  given Encoder.AsObject[Premise] = ConfiguredEncoder.derived
  given Encoder.AsObject[Problem] = ConfiguredEncoder.derived
  given Encoder.AsObject[Stop] = Encoder.AsObject.instance {
    case Stop.Invalid(ps) => JsonObject("type" -> "Invalid".asJson, "problems" -> ps.toList.asJson)
    case other            => ConfiguredEncoder.derived[Stop].encodeObject(other)
  }
  given Encoder.AsObject[Decided] = Encoder.AsObject.instance(d =>
    JsonObject("recorded" -> Json.arr(d.recorded.map((id, x) =>
      Json.obj("node" -> id.asJson, "decision" -> x.asJson))*)))
