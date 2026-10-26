package frflow.eval

/** An expression compiled once into a Scala function of its environment: what examples, probes, tests and `service`
  * call, many times. Failures are values: a run of a compiled expression never throws for a model error.
  */
final case class Compiled(run: Env => Either[EvalError, ScalaValue])
