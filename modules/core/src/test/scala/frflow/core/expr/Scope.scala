package frflow.core.expr

/** The number variables bound around a generated term, innermost first, as one interpreter holds them. */
final case class Scope[T[_]](nums: List[T[BigInt]]):
  def bind(x: T[BigInt]): Scope[T] = Scope(x :: nums)
