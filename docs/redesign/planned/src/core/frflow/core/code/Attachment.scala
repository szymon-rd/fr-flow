package frflow.core.code

import frflow.core.name.RelPath

/** What gives a Definition its meaning, and the model file it is written in. */
final case class Attachment(code: Code, writtenIn: RelPath)
