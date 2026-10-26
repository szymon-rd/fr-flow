package frflow.protocol
package snapshot

import io.circe.Codec

/** One node of the snapshot: what the developer decides (`content`, `hash`), and what the checks found. A
  * `leaf` is a claim nothing below proves (a hypothesis of root_impl). `premises`: the assumptions among its `parts`.
  */
final case class SnapNode(id: NodeId, kind: NodeKind, content: Content, hash: Hash, parents: List[NodeId] = Nil,
    parts: List[NodeId] = Nil, replaces: Option[NodeId] = None, op: Option[String] = None, defines: List[String] = Nil,
    uses: List[NodeId] = Nil, relies: List[NodeId] = Nil, rule: Boolean = false, idle: Option[String] = None,
    status: Option[CheckStatus] = None, leaf: Boolean = false, examples: List[ExampleView] = Nil, code: Option[CodeRef] = None,
    split: Option[Split] = None, invariants: List[Kept] = Nil, expectations: List[Expectation] = Nil,
    implementationProof: Option[ImplProof] = None, rootImpl: Option[Outcome] = None, covers: List[NodeId] = Nil,
    exempts: List[NodeId] = Nil, obligations: List[ObligationText] = Nil, proof: Option[ProofFile] = None,
    holds: String = "", lean: String = "", messages: List[String] = Nil, tested: Option[TestReport] = None,
    runtime: Option[RunTime] = None, premises: List[NodeId] = Nil, alwaysProofs: List[AlwaysProof] = Nil)
    derives Codec.AsObject:
  def shownKind: String = kind.shown(rule)
  def examplesPassing: (Int, Int) = (examples.count(_.passes), examples.size)
