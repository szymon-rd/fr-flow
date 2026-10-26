package frflow.core.code

import cats.data.NonEmptyList
import frflow.core.name.{BoundaryName, SymbolName}

/** What defines each Definition apart from the nodes: at most one attachment per Definition (checked against every
  * statement mentioning it), and a store's implementations, run against its model.
  */
final case class CodeTable(attached: Map[SymbolName, Attachment],
    realized: Map[BoundaryName, NonEmptyList[Realization]])
