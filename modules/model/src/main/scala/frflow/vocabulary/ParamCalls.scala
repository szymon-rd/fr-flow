package frflow
package vocabulary

/** A parameter called on terms, in a model (re-exported by `frflow`; in `Param`, an `apply` would hide its constructor). */
object ParamCalls:
  // A parameter called in a model is a term; plain code calls the value in force: `sessions.value(t)`. Called on plain values
  // it is a term too (a model may call it on constants); plain code cannot use that term as a value, nor compare it with `==`.
  extension [R](p: Param[() => R])
    def apply(): Term[R] = Term.applied(p)
  extension [A, R](p: Param[A => R])
    def apply(a: Term[A]): Term[R] = Term.applied(p, a)
  extension [A, B, R](p: Param[(A, B) => R])
    def apply(a: Term[A], b: Term[B]): Term[R] = Term.applied(p, a, b)
  extension [A, B, C, R](p: Param[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C]): Term[R] = Term.applied(p, a, b, c)
  extension [A, B, C, D, R](p: Param[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D]): Term[R] = Term.applied(p, a, b, c, e)
  extension [A, B, C, D, E, R](p: Param[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E]): Term[R] = Term.applied(p, a, b, c, e, f)
  extension [A, B, C, D, E, F, R](p: Param[(A, B, C, D, E, F) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[F]): Term[R] = Term.applied(p, a, b, c, e, f, g)
