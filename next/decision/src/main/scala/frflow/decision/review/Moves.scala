package frflow.decision.review

import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.decision.content.Content

/** What moved above a decision, and the decisions below a node that accepting it acts on: read off a reading of the
  * ledger as it counts, deciding nothing, so views ask them with no decider and no reason (docs/DAG.md §5).
  */
object Moves:
  /** The decisions below `s` that accepting it acts on, however far, each once, parents first: those accepted, and
    * those under review only because `s` (or what above it is accepted again) moved. Below a node under review for
    * anything else, nothing: it is decided first.
    */
  def actsOn(r: Reading, s: Subject): List[Subject] =
    val reached = Walk.breadthFirst(r.subjects.restingOn(s.id), (_: Subject).id)(c =>
      if listed(r, s, c) then r.subjects.restingOn(c.id) else Nil)
    r.subjects.ordered(reached.filter(listed(r, s, _)).map(_.id)).flatMap(r.subjects.get)

  /** What `c` rests on, however far up, whose meaning moved since `c` was decided, nearest first, each with its
    * content as decided then.
    */
  def movedAbove(r: Reading, c: Subject): List[(NodeId, Content)] = r.ledger.binding(c.id).fold(Nil)(d =>
    r.subjects.ancestry(c).flatMap(a => r.subjects.get(a).flatMap(now =>
      r.ledger.bindingAt(a, d.author.at).map(_.bound.content).filter(was => Meaning.of(was) != Meaning.of(now.content))
        .map(a -> _))))

  private def listed(r: Reading, s: Subject, c: Subject): Boolean = r.state(c.id) match
    case ReviewState.Accepted => true
    case ReviewState.Review   => r.causes(c.id) == List(Cause.Above) &&
      movedAbove(r, c).forall((m, _) => m == s.id || r.state(m) == ReviewState.Accepted)
    case _ => false
