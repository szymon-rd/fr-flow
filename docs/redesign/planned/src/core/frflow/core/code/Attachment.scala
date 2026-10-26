package frflow.core.code

import frflow.core.name.RelPath

/** Code attached to an operation, the run-time check the developer chose for it, and the model file it is written in.
  */
final case class Attachment(code: Code, runCheck: Option[RunCheck], writtenIn: RelPath)
