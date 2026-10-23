package frflow.api

import frflow.ledger.Reports
import frflow.protocol.*

/** Who waits on whom, and the counts every view closes with: computed here once, for every front end. */
object Queue:
  import ReviewState.{Proposed, Rejected, Review}

  /** The parents of a node that were rejected: it waits for the agent to move it. */
  def rejectedParents(v: View, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => v.node(p).exists(_.state == Rejected))

  /** Proposed or under review, and not resting on a rejected node (as `Reports.waiting` counts them). */
  def undecided(v: View): List[Reviewed] =
    v.nodes.filter(r => (r.state == Proposed || r.state == Review) && rejectedParents(v, r).isEmpty)

  private def rank(v: View): NodeId => Int =
    val at = v.annotated.order.zipWithIndex.toMap
    id => at.getOrElse(id, Int.MaxValue)

  /** The mechanical decisions waiting, in the order they are taken: one batch, one reason. */
  def mechanical(v: View): List[Reviewed] =
    undecided(v).filter(r => r.review.mechanical && !v.withAgent(r)).sortBy(r => rank(v)(r.id))

  /** What the agent has to do: remove a rejected node (reading why), answer a revisit, move a node resting
    * on a rejected one.
    */
  def forAgent(v: View): List[AgentTask] =
    def last(r: Reviewed, a: Action) = r.review.history.reverse.find(_.action == a)
    v.nodes.filter(_.state == Rejected).map { r =>
      val d = last(r, Action.Reject)
      AgentTask(r.id, TaskKind.Rejected, d.map(_.by), d.fold("")(_.reason), Nil)
    } ++ v.nodes.filter(_.review.causes.contains(Cause.Revisit)).map { r =>
      val d = last(r, Action.Revisit)
      AgentTask(r.id, TaskKind.Revisit, d.map(_.by), d.fold("")(_.reason), Nil)
    } ++ v.nodes.filter(r => r.state != Rejected && rejectedParents(v, r).nonEmpty)
      .map(r => AgentTask(r.id, TaskKind.RestsOnRejected, None, "", rejectedParents(v, r)))

  /** The inbox: the developer's queue (ready first, then the mechanical batch, then what waits for a
    * decision above it), a review moving only with a node waiting grouped under that node, the gone
    * nodes; the agent's tasks and requests; answers to read, decisions to sign, warnings.
    */
  def inbox(v: View): Inbox =
    val waiting = undecided(v).filterNot(v.withAgent).sortBy(r => rank(v)(r.id))
    val judged = waiting.filterNot(_.review.mechanical)
    val ids = judged.map(_.id).toSet
    def followers(r: Reviewed) = r.review.below.filter(b => b.kind == BelowKind.Moved && ids(b.id)).map(_.id)
    val following = judged.flatMap(followers).toSet
    val (ready, later) = judged.filterNot(r => following(r.id)).map(r => Waiting(r, r.review.waitsFor, followers(r)))
      .partition(_.waitsFor.isEmpty)
    Inbox(
      open = v.requests.filter(_.status == RequestStatus.Open),
      answers = v.requests.filter(_.status == RequestStatus.Answered),
      warnings = v.warnings,
      unsigned = v.unsigned,
      ready = ready,
      mechanical = waiting.filter(_.review.mechanical),
      later = later,
      gone = v.annotated.gone,
      withAgent = undecided(v).filter(v.withAgent),
      forAgent = forAgent(v),
      summary = summary(v))

  def summary(v: View): Summary =
    val ns = v.nodes
    def count(s: ReviewState) = ns.count(_.state == s)
    val splits = ns.filter(_.node.split.exists(_.complete.status != ObligationStatus.Informal))
    val contracts = ns.filter(_.node.kind == NodeKind.Contract)
    val waiting = undecided(v)
    Summary(
      name = v.snapshot.name,
      nodes = ns.size,
      accepted = count(ReviewState.Accepted),
      proposed = count(Proposed),
      review = count(Review),
      rejected = count(Rejected),
      gone = v.annotated.gone.size,
      forDeveloper = waiting.count(r => !v.withAgent(r)) + v.annotated.gone.size,
      mechanical = waiting.count(r => r.review.mechanical && !v.withAgent(r)),
      withAgent = waiting.count(v.withAgent),
      forAgent = forAgent(v).size,
      openRequests = v.requests.count(_.status == RequestStatus.Open),
      answers = v.requests.count(_.status == RequestStatus.Answered),
      unsigned = v.unsigned.size,
      splits = splits.size,
      splitsProven = splits.count(_.node.split.exists(_.proven)),
      contracts = contracts.size,
      contractsProvenDown = contracts.count(r => Proofs.provenDown(r.node)),
      unproven = ns.count(_.review.unproven.nonEmpty),
      rootImpl = v.snapshot.root.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status),
      trusted = v.snapshot.trusted,
      warnings = v.warnings.size,
      complete = Reports.complete(v.annotated) && v.warnings.isEmpty)
