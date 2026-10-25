package frflow

/** The stock in production: a mutable counter. */
final class Counter(var held: BigInt) extends Stock:
  def count = Flow.effect(held)
  def add(n: Term[BigInt]) = Flow.effect(n)(k => held += k)
