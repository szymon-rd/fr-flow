package frflow.eval

import frflow.core.code.Values

/** A lambda of the IR compiled once into a Scala function of its environment and its arguments: a post, a view, a
  * rule, a define called from plain code.
  */
final case class Applied(run: (Env, List[ScalaValue]) => Either[EvalError, ScalaValue]):
  /** As plain code calls it: under the values it is given, a value with no Scala semantics thrown as `NotEvaluated`
    * (the plain-code path has no `Either` to return).
    */
  def called(values: Values)(args: List[ScalaValue]): ScalaValue =
    run(Env.of(values), args).fold(e => throw NotEvaluated(e), identity)
