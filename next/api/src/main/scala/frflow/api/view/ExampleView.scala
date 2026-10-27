package frflow.api.view

import frflow.eval.run.OnCode

/** An example as checked: against the claims (Lean's status of `example_<i>`, or Scala only), and against the code. */
final case class ExampleView(name: String, onClaims: OnClaims, onCode: OnCode)
