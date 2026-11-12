package frflow.core.code

import frflow.core.name.{ModelName, SymbolName}

/** What defines each Definition apart from the nodes: at most one attachment per Definition (checked against every
  * statement mentioning it), and, per model, the plain Scala of its operations (tested against the model). The
  * members of a structure given a class (`unclaimed`) have their code whether or not a statement mentions them: an
  * example may call one no claim speaks of.
  */
final case class CodeTable(attached: Map[SymbolName, Attachment], implemented: Map[ModelName, Implementation],
    unclaimed: Set[SymbolName] = Set.empty)
