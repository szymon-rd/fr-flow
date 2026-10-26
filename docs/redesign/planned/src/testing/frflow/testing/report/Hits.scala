package frflow.testing.report

import cats.kernel.CommutativeMonoid

/** How often each part of a claim's formula went each way in the tests (each premise, disjunct, branch and match
  * arm). A commutative monoid: a run's hits are the sum of its cases', in any order.
  */
final case class Hits(counts: Map[(Position, Int), Int])

object Hits:
  given CommutativeMonoid[Hits] = new CommutativeMonoid[Hits]:
    val empty: Hits = Hits(Map.empty)
    def combine(a: Hits, b: Hits): Hits =
      Hits(b.counts.foldLeft(a.counts)((m, kv) => m.updated(kv._1, m.getOrElse(kv._1, 0) + kv._2)))
