package frflow.wire.ledger

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.content.Content
import frflow.decision.ledger.Ledger
import frflow.wire.file.FileFormat
import frflow.wire.ledger.ContentCodecs.given
import io.circe.syntax.*
import io.circe.{Decoder, Encoder, HCursor, Json, JsonObject}

/** `.frflow/ledger.json`: the decisions per node, nodes in the order of their ids, each node's oldest first; then
  * each content they are bound to, once, by its `ref` (the form a signature covers), in the order first named.
  * A content is read as written, not checked against its ref: a content edited in the file no longer matches the
  * signatures that cover its ref, and the decision rules refuse those decisions.
  */
object LedgerFile:
  val format: FileFormat[Ledger] = FileFormat(".frflow/ledger.json", 1, encoder, decoder)

  private def encoder: Encoder.AsObject[Ledger] = Encoder.AsObject.instance { l =>
    val nodes = l.decisions.toList.sortBy(_._1)
    val contents = nodes.flatMap(_._2.map(_.bound.content)).distinctBy(_.ref)
    JsonObject(
      "decisions" -> Json.fromFields(nodes.map((id, ds) => id.value -> Json.fromValues(ds.map(DecisionCodecs.encode)))),
      "contents" -> Json.fromFields(contents.map(c => c.ref -> c.asJson)))
  }

  private def decoder: Decoder[Ledger] = Decoder.instance(c =>
    for
      contents  <- fields(c, "contents")(Decoder[Content])
      decisions <- fields(c, "decisions")(Decoder.decodeList(using DecisionCodecs.decoder(contents.toMap)))
    yield Ledger(decisions.map((id, ds) => NodeId(id) -> ds).toMap))

  /** Each field of the object at `name`, in its order, read by `d` (so a failure names its path). */
  private def fields[A](c: HCursor, name: String)(d: Decoder[A]): Decoder.Result[List[(String, A)]] =
    c.get[JsonObject](name).flatMap(_.keys.toList.traverse(k => c.downField(name).get[A](k)(using d).map(k -> _)))
