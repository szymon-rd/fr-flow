package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, Json}
import io.circe.derivation.{Configuration, ConfiguredCodec}
import io.circe.syntax.*
import java.time.Instant

private given Configuration = Configuration.default.withDefaults

/** A decision of the developer about a node, bound to the hash of its `content` as they saw it, and to
  * the meaning of what it rested on (`chain`). `after` is the decision it follows (see `forked`).
  */
final case class Decision(action: Action, by: String, at: Instant, reason: String, rejected: List[NodeId] = Nil,
    after: Option[EntryRef] = None, code: Option[Fingerprint] = None, commit: Option[String] = None,
    key: Option[KeyId] = None, sig: Option[String] = None, chain: Chain = Chain.empty,
    content: Content = Content.empty) derives ConfiguredCodec:
  def hash: Hash = content.hash
  def unsigned: Decision = copy(key = None, sig = None)

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

  /** On disk, nodes in the order of their ids. */
  given Codec[Ledger] = Codec.from(Decoder[Map[NodeId, List[Decision]]].at("decisions").map(Ledger(_)),
    Encoder.instance(l => Json.obj("decisions" -> Json.fromFields(l.decisions.toList.sortBy(_._1).map((id, ds) => id.value -> ds.asJson)))))

/** A request of the developer's, on a node or on the idea; the node is with the agent until it is answered
  * (`answeredAt`) or the node changes from the `version` it was `seen` at.
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, by: String, at: Instant,
    status: RequestStatus, answer: Option[String] = None, seen: Option[Version] = None, answeredAt: Option[Instant] = None)
    derives Codec.AsObject

final case class Moved(id: NodeId, before: Content) derives Codec.AsObject
final case class RejectedBeside(id: NodeId, statement: String, why: String, reason: String) derives Codec.AsObject
final case class Alternative(id: NodeId, content: Content) derives Codec.AsObject
final case class Below(id: NodeId, kind: BelowKind, statement: String, reason: String, chosen: String, why: String) derives Codec.AsObject

/** Where the developer stands on a node, and what they read to decide it. A decision sent with `version`
  * is refused if the node moved since.
  */
final case class Review(state: ReviewState, causes: List[Cause], version: Version, waitsFor: Option[NodeId], moved: List[Moved],
    decision: Option[Decision], binding: Option[Decision], reasonNow: Option[String], notMechanical: Option[String],
    unproven: List[String], rejectedBeside: List[RejectedBeside], below: List[Below], history: List[Decision],
    rivals: List[NodeId], alternatives: List[Alternative]) derives Codec.AsObject:
  def mechanical: Boolean = notMechanical.isEmpty

final case class Reviewed(node: SnapNode, review: Review) derives Codec.AsObject:
  def id: NodeId = node.id
  def state: ReviewState = review.state

final case class Gone(id: NodeId, decision: Decision) derives Codec.AsObject

/** The snapshot with the developer's decisions, and the order they are taken in (every node after what it rests on);
  * `idea`, where the developer stands on IDEA.md (none while there is no IDEA.md).
  */
final case class Annotated(snapshot: Snapshot, nodes: List[Reviewed], gone: List[Gone], order: List[NodeId],
    idea: Option[IdeaReview] = None) derives ConfiguredCodec:
  lazy val byId: Map[NodeId, Reviewed] = nodes.map(r => r.id -> r).toMap
