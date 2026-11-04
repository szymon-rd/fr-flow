package frflow.core.code

import frflow.core.name.{ModelName, SymbolName}

/** What defines each Definition apart from the nodes: at most one attachment per Definition (checked against every
  * statement mentioning it), and, per model, the plain Scala of its operations (tested against the model).
  */
final case class CodeTable(attached: Map[SymbolName, Attachment], implemented: Map[ModelName, Implementation])
