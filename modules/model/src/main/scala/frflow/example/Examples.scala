package frflow
package example

/** `expect` and `never`: a contract's cases, by how many inputs its operation takes. */
object Examples:
  // `expect`: the contract accepts this result, and the implementation must return it. `never`: the contract must refuse it.
  // One of each per number of inputs; a flow's run takes the world before after its inputs, and the world after its result.
  def expect[R](result: R, note: String): Case[() => R] = Case(Nil, result, true, note)
  def never[R](result: R, note: String): Case[() => R] = Case(Nil, result, false, note)
  def expect[A, R](a: A, result: R, note: String): Case[A => R] = Case(List(a), result, true, note)
  def never[A, R](a: A, result: R, note: String): Case[A => R] = Case(List(a), result, false, note)
  def expect[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, true, note)
  def never[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, false, note)
  def expect[A, B, C, R](a: A, b: B, c: C, result: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), result, true, note)
  def never[A, B, C, R](a: A, b: B, c: C, result: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), result, false, note)
  def expect[A, B, C, D, R](a: A, b: B, c: C, d: D, result: R, note: String): Case[(A, B, C, D) => R] =
    Case(List(a, b, c, d), result, true, note)
  def never[A, B, C, D, R](a: A, b: B, c: C, d: D, result: R, note: String): Case[(A, B, C, D) => R] =
    Case(List(a, b, c, d), result, false, note)
  def expect[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, result: R, note: String): Case[(A, B, C, D, E) => R] =
    Case(List(a, b, c, d, e), result, true, note)
  def never[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, result: R, note: String): Case[(A, B, C, D, E) => R] =
    Case(List(a, b, c, d, e), result, false, note)
  def expect[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, result: R, note: String): Case[(A, B, C, D, E, X) => R] =
    Case(List(a, b, c, d, e, x), result, true, note)
  def never[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, result: R, note: String): Case[(A, B, C, D, E, X) => R] =
    Case(List(a, b, c, d, e, x), result, false, note)

  /** A flow's run: from the world before, its result (or `Failed(error)` for a run that fails) and the world after. */
  def expect[R](before: World, result: R | Failed, after: World, note: String): Case[() => Flow[R]] =
    Case(List(before), (result, after), true, note)
  def never[R](before: World, result: R | Failed, after: World, note: String): Case[() => Flow[R]] =
    Case(List(before), (result, after), false, note)
  def expect[A, R](a: A, before: World, result: R | Failed, after: World, note: String): Case[A => Flow[R]] =
    Case(List(a, before), (result, after), true, note)
  def never[A, R](a: A, before: World, result: R | Failed, after: World, note: String): Case[A => Flow[R]] =
    Case(List(a, before), (result, after), false, note)
  def expect[A, B, R](a: A, b: B, before: World, result: R | Failed, after: World, note: String): Case[(A, B) => Flow[R]] =
    Case(List(a, b, before), (result, after), true, note)
  def never[A, B, R](a: A, b: B, before: World, result: R | Failed, after: World, note: String): Case[(A, B) => Flow[R]] =
    Case(List(a, b, before), (result, after), false, note)
  def expect[A, B, C, R](a: A, b: B, c: C, before: World, result: R | Failed, after: World, note: String): Case[(A, B, C) => Flow[R]] =
    Case(List(a, b, c, before), (result, after), true, note)
  def never[A, B, C, R](a: A, b: B, c: C, before: World, result: R | Failed, after: World, note: String): Case[(A, B, C) => Flow[R]] =
    Case(List(a, b, c, before), (result, after), false, note)
  def expect[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, result: R | Failed, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
    Case(List(a, b, c, d, before), (result, after), true, note)
  def never[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, result: R | Failed, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
    Case(List(a, b, c, d, before), (result, after), false, note)
  def expect[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, result: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (result, after), true, note)
  def never[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, result: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (result, after), false, note)
  def expect[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, result: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (result, after), true, note)
  def never[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, result: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (result, after), false, note)
