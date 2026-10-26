package frflow
package vocabulary

/** A define called on terms, in a model (outside `Def`, where an `apply` would hide its constructor). */
object DefCalls:
  private def called[R](d: Def[?], args: Term[?]*): Term[R] =
    Term(Tree.Call(d, args.toList.map(_.termTree)), d.resultType.asInstanceOf[LeanType[R]])

  // A define called in a model is a term; plain code runs it with `fn`: `matches.fn(query, record)`. Called on plain values it
  // is a term too (a model may call it on constants); plain code cannot use that term as a value, nor compare it with `==`.
  extension [R](d: Def[() => R])
    def apply(): Term[R] = called(d)
  extension [A, R](d: Def[A => R])
    def apply(a: Term[A]): Term[R] = called(d, a)
  extension [A, B, R](d: Def[(A, B) => R])
    def apply(a: Term[A], b: Term[B]): Term[R] = called(d, a, b)
  extension [A, B, C, R](d: Def[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C]): Term[R] = called(d, a, b, c)
  extension [A, B, C, D, R](d: Def[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D]): Term[R] = called(d, a, b, c, e)
  extension [A, B, C, D, E, R](d: Def[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E]): Term[R] = called(d, a, b, c, e, f)
  extension [A, B, C, D, E, F, R](d: Def[(A, B, C, D, E, F) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[F]): Term[R] = called(d, a, b, c, e, f, g)
