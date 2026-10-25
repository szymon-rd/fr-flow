package frflow.api
package report

import frflow.ledger.Waiting
import frflow.protocol.*
import io.circe.Codec

/** What waits for the developer, in the order the ledger takes decisions: IDEA.md first when it waits (`idea`), the
  * mechanical batch, the nodes ready and those after others, the decided nodes gone; `aside`, the nodes waiting that a
  * layer on top holds back from the queue (an AI agent's, while the developer's request on them is open).
  */
final case class Inbox(warnings: List[String], ready: List[Queued], mechanical: List[Reviewed], later: List[Queued],
    gone: List[Gone], aside: List[Reviewed], overview: Overview, idea: Option[IdeaReview] = None) derives Codec.AsObject:
  def queue: List[Queued] = ready ++ later

object Inbox:
  /** A review moving only with a node waiting is grouped under it: accepting the node confirms it once all it
    * rests on holds (as the ledger's `Decide` does). `held`: the nodes a layer on top holds back (not mechanical ones).
    */
  def of(v: View, held: Set[NodeId] = Set.empty): Inbox =
    val waiting = Waiting.forDeveloper(v.annotated)
    val (mechanical, judged) = waiting.partition(_.review.mechanical)
    val (aside, mine) = judged.partition(r => held(r.id))
    val ids = mine.map(_.id).toSet
    def holds(id: NodeId) = v.node(id).forall(_.state == ReviewState.Accepted)
    def followers(r: Reviewed) =
      val moved = r.review.below.filter(b => b.kind == BelowKind.Moved && ids(b.id)).map(_.id)
      moved.filter(id => v.node(id).exists { b =>
        b.review.causes == List(Cause.Above) && (b.node.parents ++ b.node.uses ++ b.node.relies).forall(x => x == r.id || moved.contains(x) || holds(x))
      })
    val queued = mine.map(r => Queued(r, r.review.waitsFor, followers(r)))
    val following = queued.flatMap(_.followers).toSet
    val (later, ready) = queued.filterNot(q => following(q.node.id)).partition(_.waitsFor.isDefined)
    Inbox(v.warnings, ready, mechanical, later, v.annotated.gone, aside, Overview.of(v, waiting), v.ideaWaits)
