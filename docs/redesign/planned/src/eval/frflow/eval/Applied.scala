package frflow.eval

/** A lambda of the IR compiled once into a Scala function of its environment and its arguments: a check, a view, a
  * rule, a define called from plain code.
  */
final case class Applied(run: (Env, List[ScalaValue]) => Either[EvalError, ScalaValue]):
  /** As plain code calls it: under the values in force, a value with no Scala meaning thrown as `NotEvaluated` (the
    * plain-code path has no `Either` to return).
    */
  def called(args: List[ScalaValue]): ScalaValue = run(Env.inForce, args).fold(e => throw NotEvaluated(e), identity)
