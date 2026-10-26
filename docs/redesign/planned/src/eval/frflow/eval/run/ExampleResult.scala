package frflow.eval.run

import frflow.eval.*

/** An example run in Scala: against the promise, and against the attached code when there is some. */
final case class ExampleResult(index: Int, onPromise: Agreement, onCode: Option[Agreement])
