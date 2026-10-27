package frflow.core.term.algebra

/** Unbounded integers: arithmetic and order. */
trait Arith[T[_]]:
  def add(a: T[BigInt], b: T[BigInt]): T[BigInt]
  def sub(a: T[BigInt], b: T[BigInt]): T[BigInt]
  def lt(a: T[BigInt], b: T[BigInt]): T[Boolean]
  def le(a: T[BigInt], b: T[BigInt]): T[Boolean]
