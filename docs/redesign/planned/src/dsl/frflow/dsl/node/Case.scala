package frflow.dsl.node

/** One example's call, typed by the operation `F` it is a call of (`expect(a, b, result, note)`). */
final case class Case[F](inputs: List[Any], result: Any, accepted: Boolean, note: String)

object Case:
  def expect[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, true, note)
  def reject[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, false, note)
  // … for 0 to 6 inputs, and a flow's run (`expect(a, before, result, after, note)`).
