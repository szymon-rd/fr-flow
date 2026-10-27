package frflow.testing.report

import cats.kernel.CommutativeMonoid

/** How often each condition of a claim held and did not in the tests. A commutative monoid: a run's hits are the sum
  * of its cases', in any order.
  */
final case class Hits(counts: Map[(Position, Boolean), Int]):
  /** The conditions counted that no case met: what they imply was never tested. */
  def unreached: List[Position] =
    counts.keySet.map(_._1).toList.filterNot(p => counts.getOrElse((p, true), 0) > 0).sortBy(_.condition)

object Hits:
  def of(p: Position, held: Boolean): Hits = Hits(Map((p, held) -> 1))

  given CommutativeMonoid[Hits] = new CommutativeMonoid[Hits]:
    val empty: Hits = Hits(Map.empty)
    def combine(a: Hits, b: Hits): Hits =
      Hits(b.counts.foldLeft(a.counts)((m, kv) => m.updated(kv._1, m.getOrElse(kv._1, 0) + kv._2)))
