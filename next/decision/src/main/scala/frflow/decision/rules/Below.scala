package frflow.decision.rules

import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.decision.content.Content
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** After a node is accepted: the decisions below it that moved only with it confirmed, each once all it rests on
  * holds, parents first; those named revisited (docs/DAG.md §5).
  */
final class Below(r: Reading, by: Authorship, reason: String):
  def settle(s: Subject, revisit: List[NodeId], after: Ledger): Ledger =
    val confirmed = movedOnlyWith(s).filterNot(c => revisit.contains(c.id)).foldLeft(after)((l, c) =>
      if c.place.restsOn.forall(Reading(r.subjects, l).state(_) == ReviewState.Accepted)
      then l.add(c.id, record(Action.Confirm, c, s"still holds after ${s.id.value} changed: $reason"))
      else l)
    actsOn(s).filter(c => revisit.contains(c.id)).foldLeft(confirmed)((l, c) =>
      l.add(c.id, record(Action.Revisit, c, s"${s.id.value} changed and may affect it: $reason")))

  /** The decisions below `s` that accepting it acts on, however far, each once, parents first: those accepted, and
    * those under review only because `s` (or what above it is accepted again) moved. Below a node under review for
    * anything else, nothing: it is decided first.
    */
  def actsOn(s: Subject): List[Subject] =
    val reached = Walk.breadthFirst(r.subjects.restingOn(s.id), (_: Subject).id)(c =>
      if listed(s, c) then r.subjects.restingOn(c.id) else Nil)
    r.subjects.ordered(reached.filter(listed(s, _)).map(_.id)).flatMap(r.subjects.get)

  /** The decisions below `s`, however far, under review only because `s` (or what above it is accepted again) moved. */
  private def movedOnlyWith(s: Subject): List[Subject] = actsOn(s).filter(c => r.state(c.id) == ReviewState.Review)

  private def listed(s: Subject, c: Subject): Boolean = r.state(c.id) match
    case ReviewState.Accepted => true
    case ReviewState.Review   => r.causes(c.id) == List(Cause.Above) &&
      movedAbove(c).forall((m, _) => m == s.id || r.state(m) == ReviewState.Accepted)
    case _ => false

  /** What `c` rests on, however far up, whose meaning moved since `c` was decided, nearest first, each with its
    * content as decided then.
    */
  def movedAbove(c: Subject): List[(NodeId, Content)] = r.ledger.binding(c.id).fold(Nil)(d =>
    r.subjects.ancestry(c).flatMap(a => r.subjects.get(a).flatMap(now =>
      r.ledger.bindingAt(a, d.author.at).map(_.bound.content).filter(was => Meaning.of(was) != Meaning.of(now.content))
        .map(a -> _))))

  private def record(a: Action, c: Subject, why: String) = Decision.taken(a, by, Reason(why, Nil), r.bound(c))
