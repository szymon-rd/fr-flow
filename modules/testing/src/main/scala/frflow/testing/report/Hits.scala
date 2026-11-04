package frflow.testing.report

import cats.kernel.CommutativeMonoid

/** How often each target was reached in the tests. A commutative monoid: a run's hits are the sum of its cases', in
  * any order; a run starts from every target at zero (`zero`), so one no case reached is said.
  */
final case class Hits(counts: Map[Target, Int]):
  def unreached: List[Target] =
    counts.collect { case (t, 0) => t }.toList.sortBy(t => (t.at.path.mkString("."), t.reach.toString))

object Hits:
  def zero(targets: List[Target]): Hits = Hits(targets.map(_ -> 0).toMap)
  def of(t: Target): Hits = Hits(Map(t -> 1))

  given CommutativeMonoid[Hits] = new CommutativeMonoid[Hits]:
    val empty: Hits = Hits(Map.empty)
    def combine(a: Hits, b: Hits): Hits =
      Hits(b.counts.foldLeft(a.counts)((m, kv) => m.updated(kv._1, m.getOrElse(kv._1, 0) + kv._2)))
