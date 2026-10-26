package frflow.core.code

import cats.data.NonEmptyList
import frflow.core.name.NodeId

/** The code of a knowledge base, apart from its nodes: at most one attachment per node, by type. */
final case class CodeTable(attached: Map[NodeId, Attachment], realized: Map[NodeId, NonEmptyList[Realization]])
