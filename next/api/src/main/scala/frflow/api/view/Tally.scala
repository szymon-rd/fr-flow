package frflow.api.view

import cats.kernel.{CommutativeMonoid, Eq}

/** Counts by kind (`Tally[ReviewState]`: how many proposed, accepted, …): a commutative monoid, so the overview is
  * one `foldMap` over the nodes. A kind counted zero times is not held, so two tallies are equal exactly when they
  * count alike.
  */
final case class Tally[K] private (counts: Map[K, Int]):
  def apply(k: K): Int = counts.getOrElse(k, 0)

object Tally:
  def apply[K](counts: Map[K, Int]): Tally[K] = new Tally(counts.filter(_._2 != 0))
  def one[K](k: K): Tally[K] = Tally(Map(k -> 1))

  given [K]: Eq[Tally[K]] = Eq.fromUniversalEquals
  given [K]: CommutativeMonoid[Tally[K]] = new CommutativeMonoid[Tally[K]]:
    val empty: Tally[K] = Tally(Map.empty)
    def combine(a: Tally[K], b: Tally[K]): Tally[K] =
      Tally(b.counts.foldLeft(a.counts)((m, kv) => m.updated(kv._1, m.getOrElse(kv._1, 0) + kv._2)))
