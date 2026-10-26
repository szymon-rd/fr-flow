package frflow.wire.snapshot

/** An example as Scala ran it: against the promise, and against the attached code when there is some. */
final case class ExampleRow(index: Int, onPromise: AgreementRow, onCode: Option[AgreementRow])
