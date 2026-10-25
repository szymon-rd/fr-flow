package frflow.protocol
package decision

import cats.syntax.all.*
import io.circe.{Codec, Decoder, DecodingFailure, Encoder, Json, JsonObject}
import io.circe.syntax.*

/** The developer's decisions, per node, oldest first (`.frflow/ledger.json`). Nothing in it is ever overwritten. */
final case class Ledger(decisions: Map[NodeId, List[Decision]]):
  def history(id: NodeId): List[Decision] = decisions.getOrElse(id, Nil)
  def current(id: NodeId): Option[Decision] = history(id).lastOption
  private def sinceRejected(id: NodeId) =
    history(id).reverse.takeWhile(d => d.action != Action.Reject && d.action != Action.Remove).reverse
  /** The acceptance that chose the node (the first since it was last rejected or removed): later ones are of changes. */
  def chosen(id: NodeId): Option[Decision] = sinceRejected(id).find(_.action == Action.Accept)
  def sinceChosen(id: NodeId): List[Decision] = sinceRejected(id).dropWhile(_.action != Action.Accept)

  /** Its last acceptance or confirmation, also while it is being revisited. */
  def binding(id: NodeId): Option[Decision] = current(id) match
    case Some(d) if d.action == Action.Revisit => history(id).reverse.find(_.action.binds)
    case c => c.filter(_.action.binds)

  def add(id: NodeId, d: Decision): Ledger =
    Ledger(decisions.updated(id, history(id) :+ d.copy(after = current(id).map(Ledger.entry))))

  /** Two branches decided the node, and a merge kept both: it is decided again. */
  def forked(id: NodeId): Boolean =
    current(id).exists(d => d.after.fold(history(id).size > 1)(a => history(id).count(_.after.contains(a)) > 1))

  def alternatives(id: NodeId): List[(NodeId, Content)] =
    history(id).filter(_.action == Action.Accept).flatMap(_.rejected).distinct
      .flatMap(r => history(r).reverse.find(_.action == Action.Reject).map(d => r -> d.content))

  def rejectedUnder(parent: NodeId): List[(NodeId, Content, String)] = rejectedByParent.getOrElse(parent, Nil)
  // Once per ledger: a view asks it of every node's parents.
  private lazy val rejectedByParent: Map[NodeId, List[(NodeId, Content, String)]] =
    decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.lastOption.filter(_.action == Action.Reject).toList
      .flatMap(d => d.content.parents.distinct.map(_ -> (id, d.content, d.reason)))).groupMap(_._1)(_._2)

  /** Every decision, newest first. */
  def all: List[(NodeId, Decision)] = decisions.toList.flatMap((id, ds) => ds.map(id -> _)).sortBy(_._2.at).reverse

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  def entry(d: Decision): EntryRef =
    EntryRef(Sha.parts(d.action.toString, d.by, d.at.toString, d.reason, d.content.ref).take(16))

  /** On disk (`.frflow/ledger.json`), nodes in the order of their ids, and each part of a content written once:
    *  - a decision names its content by `content.ref`, the reference its signature covers;
    *  - `contents` holds each content once, as its fields in order, each field the reference of its value, a list
    *    field the references of its elements;
    *  - `values` holds each value or element once, by the first 16 hex digits of the SHA-256 of its canonical print.
    * So a decision that changes one example of a node adds that example, not the node again. A content is checked as
    * it is read: it must hash to its name. A ledger with the contents written inside its decisions reads too.
    */
  given Codec[Ledger] = Codec.from(OnDisk.decoder, OnDisk.encoder)

  /** The file's text: the decisions indented as FrFlow's files are, each content and each value on a line of its own. */
  def file(l: Ledger): String =
    val o = l.asJson.asObject.getOrElse(JsonObject.empty)
    def lines(table: String) = o(table).flatMap(_.asObject).filter(_.nonEmpty).fold("{}")(_.toList
      .map((ref, v) => s"    ${Canonical.print(Json.fromString(ref))}: ${Canonical.print(v)}").mkString("{\n", ",\n", "\n  }"))
    s"{\n  \"decisions\": ${o("decisions").fold("{}")(Canonical.file(_, 1))},\n  \"contents\": ${lines("contents")},\n" +
      s"  \"values\": ${lines("values")}\n}\n"

  private object OnDisk:
    def name(j: Json): String = Sha(Canonical.print(j)).take(16)
    private def elements(v: Json): List[Json] = v.asArray.fold(List(v))(_.toList)
    private def fields(c: Content): Json =
      Json.fromFields(c.fields.map((k, v) => k -> v.asArray.fold(Json.fromString(name(v)))(xs => Json.fromValues(xs.map(x => Json.fromString(name(x)))))))

    val encoder: Encoder[Ledger] = Encoder.instance { l =>
      val nodes = l.decisions.toList.sortBy(_._1)
      val contents = nodes.flatMap(_._2.map(_.content)).distinctBy(_.ref)
      Json.obj(
        "decisions" -> Json.fromFields(nodes.map((id, ds) =>
          id.value -> Json.fromValues(ds.map(d => d.asJson.mapObject(_.add("content", Json.fromString(d.content.ref))))))),
        "contents" -> Json.fromFields(contents.map(c => c.ref -> fields(c))),
        "values" -> Json.fromFields(contents.flatMap(_.fields.flatMap((_, v) => elements(v))).distinctBy(name).map(v => name(v) -> v)))
    }

    val decoder: Decoder[Ledger] = Decoder.instance { c =>
      def fail(why: String) = DecodingFailure(why, c.history)
      for
        values   <- c.getOrElse[Map[String, Json]]("values")(Map.empty)
        written  <- c.getOrElse[Map[String, JsonObject]]("contents")(Map.empty)
        value     = (r: Json) => r.asString.flatMap(values.get).toRight(fail(s"no value $r in the ledger's values"))
        contents <- written.toList.traverse { (ref, fs) =>
                      fs.toList.traverse((k, r) => r.asArray.fold(value(r))(_.toList.traverse(value).map(Json.fromValues)).map(k -> _))
                        .map(Content(_*)).filterOrElse(_.ref == ref, fail(s"the content $ref in the ledger does not hash to its name"))
                        .map(ref -> _)
                    }.map(_.toMap)
        raw      <- c.get[Map[NodeId, List[Json]]]("decisions")
        ledger   <- raw.toList.traverse((id, ds) => ds.traverse(d => d.hcursor.get[String]("content").toOption.fold(d.as[Decision])(ref =>
                      contents.get(ref).toRight(fail(s"$id names the content $ref, which the ledger does not hold"))
                        .flatMap(content => d.mapObject(_.add("content", content.json)).as[Decision]))).map(id -> _))
      yield Ledger(ledger.toMap)
    }
