package frflow.api

import frflow.ledger.{ForAgent, Queue, Summary, Waiting}
import frflow.protocol.*
import io.circe.Codec

/** The counts every view closes with: the decisions (the ledger's `Summary`: by state, proven, what waits
  * for the developer), what is with the agent, the requests and signatures, how far the proofs reach (see
  * `Status.Reach`), and whether the knowledge base is complete.
  */
final case class Overview(
    name: String,
    decisions: Summary,
    withAgent: Int,
    forAgent: Int,
    openRequests: Int,
    answers: Int,
    unsigned: Int,
    splits: Int,
    splitsProven: Int,
    contracts: Int,
    contractsProvenDown: Int,
    rootImpl: Option[ObligationStatus],
    warnings: Int,
    complete: Boolean
) derives Codec.AsObject:
  /** The decisions waiting for the developer: all that wait, less those asked of the agent. */
  def forDeveloper: Int = decisions.load.total - withAgent
  def unproven: Int = decisions.nodes - decisions.proven

object Overview:
  def of(v: View): Overview =
    val reach = v.status.reach
    Overview(
      name = v.snapshot.name,
      decisions = Summary.of(v.annotated),
      withAgent = Inbox.asked(v).size,
      forAgent = Waiting.of(v.annotated).agent.size,
      openRequests = v.requests.count(_.status == RequestStatus.Open),
      answers = v.requests.count(_.status == RequestStatus.Answered),
      unsigned = v.unsigned.size,
      splits = reach.splits,
      splitsProven = reach.provenSplits,
      contracts = reach.contracts,
      contractsProvenDown = reach.provenDown.size,
      rootImpl = v.snapshot.root.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status),
      warnings = v.warnings.size,
      complete = v.status.ok)

/** A node waiting for the developer, with what it waits for and the reviews that move with it. */
final case class Queued(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject

/** What waits for whom: the developer's queue (ready, the mechanical batch, later, gone) in the order the
  * ledger takes decisions (`Queue`), less what is asked of the agent; the agent's work (`Waiting`) and
  * requests; the answers to read, the decisions to sign, and the warnings.
  */
final case class Inbox(
    open: List[Request],
    answers: List[Request],
    warnings: List[String],
    unsigned: List[Unsigned],
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

  /** A review moving only with a node waiting is grouped under that node: accepting it confirms them. */
  def of(v: View): Inbox =
    val q = Queue.of(v.annotated)
    def judged(ids: List[NodeId]) = ids.flatMap(v.node).filterNot(v.withAgent)
    val waiting = judged(q.ready ++ q.waiting).map(_.id).toSet
    def followers(r: Reviewed) = r.review.below.filter(b => b.kind == BelowKind.Moved && waiting(b.id)).map(_.id)
    def queued(ids: List[NodeId]) = judged(ids).map(r => Queued(r, r.review.waitsFor, followers(r)))
    val following = queued(q.ready ++ q.waiting).flatMap(_.followers).toSet
    Inbox(
      open = v.requests.filter(_.status == RequestStatus.Open),
      answers = v.requests.filter(_.status == RequestStatus.Answered),
      warnings = v.warnings,
      unsigned = v.unsigned,
      ready = queued(q.ready).filterNot(w => following(w.node.id)),
      mechanical = q.mechanical.flatMap(v.node),
      later = queued(q.waiting).filterNot(w => following(w.node.id)),
      gone = v.annotated.gone,
      withAgent = asked(v),
      forAgent = Waiting.of(v.annotated).agent,
      overview = Overview.of(v))
