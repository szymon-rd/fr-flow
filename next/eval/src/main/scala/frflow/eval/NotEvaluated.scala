package frflow.eval

/** Thrown to the developer's plain code when a define it calls (`d.fn`, a definition's term) has no Scala value: the
  * documented edge of the plain-code path, where there is no `Either` to return.
  */
final class NotEvaluated(val error: EvalError) extends RuntimeException(error.toString, null, false, false)
