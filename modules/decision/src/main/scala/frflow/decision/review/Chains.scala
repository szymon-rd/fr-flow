package frflow.decision.review

import frflow.core.name.NodeId
import frflow.decision.content.Chain

/** Each node's chain as the graph stands: computed once, in decision order (a design's chain is empty: it rests on
  * its parents' place, not their meaning).
  */
object Chains:
  def of(subjects: Subjects): Map[NodeId, Chain] =
    subjects.inOrder.foldLeft(Map.empty[NodeId, Chain]) { (done, s) =>
      done.updated(s.id, Meaning.chain(Meaning.of(s.content), above(s, done)))
    }

  /** What `s` rests on, as a chain. */
  def above(s: Subject, chains: Map[NodeId, Chain]): Chain =
    if s.place.design then Chain.empty else Meaning.over(s.place.restsOn.flatMap(chains.get))
