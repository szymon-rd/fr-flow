package frflow.protocol
package snapshot

import io.circe.Codec
import java.time.Instant

/** The knowledge base as data, without decisions: what `check` writes to `.frflow/kb.json`. */
final case class Snapshot(name: String, nodes: List[SnapNode], idea: String = "", ideaFile: String = "",
    warnings: List[String] = Nil, root: Option[NodeId] = None, roots: List[NodeId] = Nil,
    definitions: List[NodeId] = Nil, trusted: List[NodeId] = Nil,
    exportedAt: Instant = Instant.EPOCH, opaques: List[OpaqueTerm] = Nil, params: List[ParamTerm] = Nil,
    types: List[TypeText] = Nil, defs: List[DefText] = Nil, tested: List[NodeId] = Nil,
    consistency: Option[Consistency] = None) derives Codec.AsObject
