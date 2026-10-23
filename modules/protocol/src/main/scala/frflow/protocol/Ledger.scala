package frflow.protocol

import io.circe.{Codec, Decoder, DecodingFailure, Encoder, Json, JsonObject}
import io.circe.syntax.*

/** A decision of the developer about a node.
  *
  * @param content  the node as the developer saw it; the decision is bound to its hash
  * @param chain    the meaning of what the node rested on, as decided; when it changes, the node is reviewed
  * @param reason   why: kept as part of the theory
  * @param rejected for `accept`, the alternatives rejected by this choice
  * @param after    the node's decision this one follows (its `entry`): two decisions following the same
  *                 one come from two branches, merged; the node is then decided again
  * @param code     the fingerprint of the source files the node governs, when decided
  * @param commit   the git commit checked out when deciding
  * @param tree     the code as decided, written to git as a tree, to show how the code changed since
  *                 (a clone without it falls back to `commit`)
  * @param key      the developer key that signed it, with `sig` the signature (see `Signing`)
  */
final case class Decision(action: Action, by: String, at: String, reason: String, rejected: List[NodeId] = Nil,
    after: Option[EntryRef] = None, code: Option[Fingerprint] = None, commit: Option[String] = None,
    tree: Option[String] = None, key: Option[KeyId] = None, sig: Option[String] = None,
    chain: Chain = Chain.empty, content: Content = Content.empty) derives Codec.AsObject:
  def hash: Hash = content.hash
  /** The decision without its signature: what is signed, and what a rewrite is judged on. */
  def unsigned: Decision = copy(key = None, sig = None)

/** The developer's decisions, per node, oldest first: the record of the theory and its history.
  * Kept in `.frflow/ledger.json` and committed. Nothing in it is ever overwritten.
  */
final case class Ledger(decisions: Map[NodeId, List[Decision]]):
  /** A node's decisions, oldest first. */
  def history(id: NodeId): List[Decision] = decisions.getOrElse(id, Nil)
  def current(id: NodeId): Option[Decision] = history(id).lastOption
  private def sinceRejected(id: NodeId) =
    history(id).reverse.takeWhile(d => d.action != Action.Reject && d.action != Action.Remove).reverse
  /** The developer's choice of the node: the acceptance that chose it (the first since it was last
    * rejected or removed), which carries the reason it was chosen. Later acceptances are of changes.
    */
  def chosen(id: NodeId): Option[Decision] = sinceRejected(id).find(_.action == Action.Accept)
  /** The decisions since the node was chosen: its choice, the changes accepted and confirmations. */
  def sinceChosen(id: NodeId): List[Decision] = sinceRejected(id).dropWhile(_.action != Action.Accept)

  /** What the node is bound to now: its last acceptance or confirmation (also while the developer
    * has asked to revisit it).
    */
  def binding(id: NodeId): Option[Decision] = current(id) match
    case Some(d) if d.action == Action.Revisit => history(id).reverse.find(_.action.binds)
    case c => c.filter(_.action.binds)

  def add(id: NodeId, d: Decision): Ledger =
    Ledger(decisions.updated(id, history(id) :+ d.copy(after = current(id).map(Ledger.entry))))

  /** Two branches decided the node, and the merge kept both: the last decision is one of two that
    * follow the same one, or follows none (a first decision) though others come before it. Nothing
    * says which holds, so the node is decided again.
    */
  def forked(id: NodeId): Boolean =
    current(id).exists(d => d.after.fold(history(id).size > 1)(a => history(id).count(_.after.contains(a)) > 1))

  /** The alternatives ever rejected in favour of a node, as they were proposed. */
  def alternatives(id: NodeId): List[(NodeId, Content)] =
    history(id).filter(_.action == Action.Accept).flatMap(_.rejected).distinct
      .flatMap(r => history(r).reverse.find(_.action == Action.Reject).map(d => r -> d.content))

  /** The nodes rejected under `parent` (now or once), each with its content and the reason: the
    * options already turned down where a new proposal stands.
    */
  def rejectedUnder(parent: NodeId): List[(NodeId, Content, String)] =
    decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.lastOption.filter(d => d.action == Action.Reject &&
      d.content.parents.contains(parent)).map(d => (id, d.content, d.reason)))

  /** Every decision, newest first. */
  def all: List[(NodeId, Decision)] = decisions.toList.flatMap((id, ds) => ds.map(id -> _)).sortBy(_._2.at).reverse

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  /** A short reference to a decision: what was decided, by whom, when and why. */
  def entry(d: Decision): EntryRef =
    EntryRef(Sha.parts(d.action.toString, d.by, d.at, d.reason, d.content.ref).take(16))

  /** On disk, content already recorded for the node is written once, then referred to by its reference
    * (`"content": "same:<ref>"`), which stays right when a merge interleaves two branches' decisions.
    */
  given Codec[Ledger] = Codec.from(
    Decoder.instance { c =>
      c.downField("decisions").as[JsonObject].flatMap { o =>
        o.toList.foldLeft[Decoder.Result[Map[NodeId, List[Decision]]]](Right(Map.empty)) { case (acc, (id, ds)) =>
          acc.flatMap(m => ds.as[List[Json]].flatMap(_.foldLeft[Decoder.Result[List[Decision]]](Right(Nil))((done, d) =>
            done.flatMap(prev => decision(prev, d).map(prev :+ _)))).map(m.updated(NodeId(id), _)))
        }
      }.map(Ledger(_))
    },
    Encoder.instance { l =>
      Json.obj("decisions" -> Json.fromFields(l.decisions.toList.sortBy(_._1).map { (id, ds) =>
        id.value -> Json.fromValues(ds.zipWithIndex.map { (d, i) =>
          val o = d.asJsonObject.filter((k, v) => !(k == "rejected" && d.rejected.isEmpty))
          Json.fromJsonObject(if ds.take(i).exists(_.content == d.content) then o.add("content", Json.fromString("same:" + d.content.ref)) else o)
        })
      }))
    })

  private def decision(before: List[Decision], d: Json): Decoder.Result[Decision] =
    val c = d.hcursor
    // A decision without `rejected` rejected nothing.
    val full = d.mapObject(o => if o.contains("rejected") then o else o.add("rejected", Json.arr()))
    c.downField("content").as[String].toOption.filter(_.startsWith("same:")).map(_.stripPrefix("same:")) match
      case None => full.as[Decision]
      case Some(ref) =>
        before.reverse.find(_.content.ref == ref).toRight(DecodingFailure(s"no content $ref before", c.history))
          .flatMap(prev => full.mapObject(_.add("content", prev.content.json)).as[Decision])
