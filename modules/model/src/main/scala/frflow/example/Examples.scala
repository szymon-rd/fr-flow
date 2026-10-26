package frflow
package example

/** `allows` and `forbids`: a contract's cases, by how many inputs its operation takes; `is`, an example's answer. */
object Examples:
  extension [A](call: Term[A])
    /** The answer the call must give, in an example written as a test: `granted(held, request) is true`. */
    infix def is(answer: A): Expected = Expected(call, answer)

  // `allows`: the contract allows the call returning this, and the implementation must return it. `forbids`: the contract
  // forbids the call returning it.
  // One of each per number of inputs; a flow's run takes the world before after its inputs, and the world after its result.
  def allows[R](returning: R, note: String): Case[() => R] = Case(Nil, returning, true, note)
  def forbids[R](returning: R, note: String): Case[() => R] = Case(Nil, returning, false, note)
  def allows[A, R](a: A, returning: R, note: String): Case[A => R] = Case(List(a), returning, true, note)
  def forbids[A, R](a: A, returning: R, note: String): Case[A => R] = Case(List(a), returning, false, note)
  def allows[A, B, R](a: A, b: B, returning: R, note: String): Case[(A, B) => R] = Case(List(a, b), returning, true, note)
  def forbids[A, B, R](a: A, b: B, returning: R, note: String): Case[(A, B) => R] = Case(List(a, b), returning, false, note)
  def allows[A, B, C, R](a: A, b: B, c: C, returning: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), returning, true, note)
  def forbids[A, B, C, R](a: A, b: B, c: C, returning: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), returning, false, note)
  def allows[A, B, C, D, R](a: A, b: B, c: C, d: D, returning: R, note: String): Case[(A, B, C, D) => R] =
    Case(List(a, b, c, d), returning, true, note)
  def forbids[A, B, C, D, R](a: A, b: B, c: C, d: D, returning: R, note: String): Case[(A, B, C, D) => R] =
    Case(List(a, b, c, d), returning, false, note)
  def allows[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, returning: R, note: String): Case[(A, B, C, D, E) => R] =
    Case(List(a, b, c, d, e), returning, true, note)
  def forbids[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, returning: R, note: String): Case[(A, B, C, D, E) => R] =
    Case(List(a, b, c, d, e), returning, false, note)
  def allows[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, returning: R, note: String): Case[(A, B, C, D, E, X) => R] =
    Case(List(a, b, c, d, e, x), returning, true, note)
  def forbids[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, returning: R, note: String): Case[(A, B, C, D, E, X) => R] =
    Case(List(a, b, c, d, e, x), returning, false, note)

  /** A flow's run: from the world before, its result (or `Failed(error)` for a run that fails) and the world after. */
  def allows[R](before: World, returning: R | Failed, after: World, note: String): Case[() => Flow[R]] =
    Case(List(before), (returning, after), true, note)
  def forbids[R](before: World, returning: R | Failed, after: World, note: String): Case[() => Flow[R]] =
    Case(List(before), (returning, after), false, note)
  def allows[A, R](a: A, before: World, returning: R | Failed, after: World, note: String): Case[A => Flow[R]] =
    Case(List(a, before), (returning, after), true, note)
  def forbids[A, R](a: A, before: World, returning: R | Failed, after: World, note: String): Case[A => Flow[R]] =
    Case(List(a, before), (returning, after), false, note)
  def allows[A, B, R](a: A, b: B, before: World, returning: R | Failed, after: World, note: String): Case[(A, B) => Flow[R]] =
    Case(List(a, b, before), (returning, after), true, note)
  def forbids[A, B, R](a: A, b: B, before: World, returning: R | Failed, after: World, note: String): Case[(A, B) => Flow[R]] =
    Case(List(a, b, before), (returning, after), false, note)
  def allows[A, B, C, R](a: A, b: B, c: C, before: World, returning: R | Failed, after: World, note: String): Case[(A, B, C) => Flow[R]] =
    Case(List(a, b, c, before), (returning, after), true, note)
  def forbids[A, B, C, R](a: A, b: B, c: C, before: World, returning: R | Failed, after: World, note: String): Case[(A, B, C) => Flow[R]] =
    Case(List(a, b, c, before), (returning, after), false, note)
  def allows[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, returning: R | Failed, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
    Case(List(a, b, c, d, before), (returning, after), true, note)
  def forbids[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, returning: R | Failed, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
    Case(List(a, b, c, d, before), (returning, after), false, note)
  def allows[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, returning: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (returning, after), true, note)
  def forbids[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, returning: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (returning, after), false, note)
  def allows[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, returning: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (returning, after), true, note)
  def forbids[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, returning: R | Failed, after: World, note: String)
      : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (returning, after), false, note)
