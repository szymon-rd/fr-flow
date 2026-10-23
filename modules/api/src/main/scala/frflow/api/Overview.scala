package frflow.api

import frflow.ledger.{ForAgent, Proofs, Waiting}
import frflow.protocol.*
import io.circe.Codec

/** The counts every view closes with: the nodes by state, how many are proven, what the root's proof trusts,
  * what waits for whom, the requests and signatures, the splits and contracts proven, the examples Lean
  * evaluates as Scala does, and whether the knowledge base is complete (`View.ok`).
  */
final case class Overview(name: String, nodes: Int, proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int,
    proven: Int, trusted: List[NodeId], forDeveloper: Int, mechanical: Int, withAgent: Int, forAgent: Int, openRequests: Int,
    answers: Int, unsigned: Int, splits: Int, splitsProven: Int, contracts: Int, contractsProvenDown: Int,
    examplesInLean: Int, examplesAgreeing: Int, rootImpl: Option[ObligationStatus], warnings: Int, complete: Boolean)
    derives Codec.AsObject:
  def unproven: Int = nodes - proven

object Overview:
  def of(v: View): Overview =
    val a = v.annotated
    val ns = a.nodes.map(_.node)
    def count(s: ReviewState) = a.nodes.count(_.state == s)
    val waiting = Waiting.forDeveloper(a)
    val asked = Inbox.asked(v)
    val contracts = ns.filter(_.kind == NodeKind.Contract)
    val inLean = ns.flatMap(_.examples.flatMap(_.lean))
    Overview(v.snapshot.name, a.nodes.size, count(ReviewState.Proposed), count(ReviewState.Review), count(ReviewState.Accepted),
      count(ReviewState.Rejected), a.gone.size, ns.count(Proofs.unproven(_).isEmpty), v.snapshot.trusted,
      waiting.size + a.gone.size - asked.size, waiting.count(_.review.mechanical), asked.size, Waiting.forAgent(a).size,
      v.requests.count(_.status == RequestStatus.Open), v.requests.count(_.status == RequestStatus.Answered), v.unsigned.size,
      ns.count(_.split.isDefined), ns.count(_.split.exists(_.proven)), contracts.size,
      contracts.count(c => c.status.contains(CheckStatus.Proven) && c.implementationProof.exists(_.status == ObligationStatus.Proven)),
      inLean.size, inLean.count(_.status == ObligationStatus.Proven),
      v.snapshot.root.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status), v.warnings.size, v.ok)

/** A node waiting for the developer, with what it waits for and the reviews that move with it. */
final case class Queued(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject

/** What waits for whom: the developer's queue (ready, the mechanical batch, later, gone) in the order the
  * ledger takes decisions, less what is asked of the agent; the agent's work and requests; the answers to
  * read, and the warnings.
  */
final case class Inbox(
    open: List[Request],
    answers: List[Request],
    warnings: List[String],
    ready: List[Queued],
    mechanical: List[Reviewed],
    later: List[Queued],
    gone: List[Gone],
    withAgent: List[Reviewed],
    forAgent: List[ForAgent],
    overview: Overview
) derives Codec.AsObject:
  /** The developer's queue in the order to decide it. */
  def queue: List[Queued] = ready ++ later

object Inbox:
  /** The decisions to judge (not mechanical) that the developer asked the agent about: with the agent. */
  def asked(v: View): List[Reviewed] = Waiting.forDeveloper(v.annotated).filter(r => !r.review.mechanical && v.withAgent(r))

  /** A review moving only with a node waiting is grouped under that node: accepting it confirms them, each
    * once all it rests on holds (as the ledger's `Decide` does); one resting on another node still waiting is not.
    */
  def of(v: View): Inbox =
    val (mechanical, judged) = Waiting.forDeveloper(v.annotated).partition(_.review.mechanical)
    val mine = judged.filterNot(v.withAgent)
    val waiting = mine.map(_.id).toSet
    def holds(id: NodeId) = v.node(id).forall(_.state == ReviewState.Accepted)
    def followers(r: Reviewed) =
      val moved = r.review.below.filter(b => b.kind == BelowKind.Moved && waiting(b.id)).map(_.id)
      moved.filter(id => v.node(id).exists { b =>
        b.review.causes == List(Cause.Above) && (b.node.parents ++ b.node.uses ++ b.node.relies).forall(x => x == r.id || moved.contains(x) || holds(x))
      })
    val queued = mine.map(r => Queued(r, r.review.waitsFor, followers(r)))
    val following = queued.flatMap(_.followers).toSet
    val (later, ready) = queued.filterNot(q => following(q.node.id)).partition(_.waitsFor.isDefined)
    Inbox(
      open = v.requests.filter(_.status == RequestStatus.Open),
      answers = v.requests.filter(_.status == RequestStatus.Answered),
      warnings = v.warnings,
      ready = ready,
      mechanical = mechanical,
      later = later,
      gone = v.annotated.gone,
      withAgent = asked(v),
      forAgent = Waiting.forAgent(v.annotated),
      overview = Overview.of(v))
