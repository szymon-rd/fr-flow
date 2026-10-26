package frflow.wire.snapshot

/** Whether a run agrees with its example, as tools read it: a tag (`agrees`, `promise-refuses`, `promise-accepts`,
  * `returned`, `breaks`) and what it returned or broke.
  */
final case class AgreementRow(tag: String, detail: Option[String])
