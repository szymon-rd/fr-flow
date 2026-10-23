package frflow.protocol

import io.circe.Codec
import java.time.Instant

/** A status with what it means in words: of an obligation, a part, an example in Lean. */
final case class Outcome(status: ObligationStatus, detail: String = "") derives Codec.AsObject
object Outcome:
  val unchecked: Outcome = Outcome(ObligationStatus.Unchecked, "not checked yet")
  def of(r: Result): Outcome = Outcome(r.status, r.detail)

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`. */
final case class Split(complete: Outcome, needed: List[Split.Part], clash: Outcome) derives Codec.AsObject:
  /** Lean proves the parts make the node, none is shown not needed, and they do not clash. */
  def proven: Boolean = complete.status == ObligationStatus.Proven && needed.forall(_.status.fine) && clash.status.fine
object Split:
  final case class Part(id: NodeId, status: ObligationStatus, detail: String) derives Codec.AsObject

/** An example of a contract: what it says, what fails of it in Scala (against the contract, and against
  * the implementation), and what Lean computes of it (the examples written, not generated ones).
  */
final case class ExampleView(note: String, `given`: List[String], call: String, expected: Boolean, fails: Option[String],
    codeFails: Option[String], lean: Option[Outcome], leanImplementation: Option[Outcome]) derives Codec.AsObject:
  def passes: Boolean = fails.isEmpty && codeFails.isEmpty

/** The source files a node governs, and their fingerprint. */
final case class CodeRef(files: List[String], fingerprint: Fingerprint) derives Codec.AsObject

/** An invariant a contract keeps (with the view of what it returns), or is exempt from. */
final case class Kept(id: NodeId, view: String, rule: String, status: ObligationStatus, detail: String) derives Codec.AsObject

/** What the node expects of the world (`expects`), and whether Lean proves it. */
final case class Expectation(statement: String, source: String, status: ObligationStatus, detail: String) derives Codec.AsObject

/** A contract's proven implementation (a define), and whether Lean proves it meets the contract. */
final case class ImplProof(name: String, status: ObligationStatus, detail: String) derives Codec.AsObject

final case class ObligationText(name: String, statement: String, description: String) derives Codec.AsObject
final case class ProofFile(file: String, source: String) derives Codec.AsObject

/** One node of the snapshot: its place in the DAG, what the developer decides (`content`, `hash`), and
  * what the checks found.
  *
  * @param uses   the definitions it uses
  * @param relies the contracts its code calls
  * @param status the check of its statement; none for a definition or a design decision
  * @param leaf   a claim nothing below proves: trusted as it stands (a hypothesis of root_impl)
  * @param idle   for the root, what doing nothing is, when Lean shows it meets the root
  */
final case class SnapNode(
    id: NodeId,
    kind: NodeKind,
    content: Content,
    hash: Hash,
    parents: List[NodeId] = Nil,
    parts: List[NodeId] = Nil,
    replaces: Option[NodeId] = None,
    op: Option[String] = None,
    defines: List[String] = Nil,
    uses: List[NodeId] = Nil,
    relies: List[NodeId] = Nil,
    rule: Boolean = false,
    idle: Option[String] = None,
    status: Option[CheckStatus] = None,
    leaf: Boolean = false,
    examples: List[ExampleView] = Nil,
    code: Option[CodeRef] = None,
    split: Option[Split] = None,
    invariants: List[Kept] = Nil,
    expectations: List[Expectation] = Nil,
    implementationProof: Option[ImplProof] = None,
    rootImpl: Option[Outcome] = None,
    covers: List[NodeId] = Nil,
    exempts: List[NodeId] = Nil,
    obligations: List[ObligationText] = Nil,
    proof: Option[ProofFile] = None,
    holds: String = "",
    lean: String = "",
    messages: List[String] = Nil
) derives Codec.AsObject:
  /** Its kind as people read it: an invariant is a claim with a rule. */
  def shownKind: String = kind.shown(rule)
  /** The root: the claim with no parents. */
  def isRoot: Boolean = kind == NodeKind.Claim && parents.isEmpty
  /** How many of its examples pass, of how many. */
  def examplesPassing: (Int, Int) = (examples.count(_.passes), examples.size)

final case class OpaqueTerm(name: String, means: String, definedBy: Option[NodeId]) derives Codec.AsObject
final case class ParamTerm(name: String, means: String, operation: Boolean, definedBy: Option[NodeId], lean: String) derives Codec.AsObject
final case class TypeText(name: String, lean: String) derives Codec.AsObject
final case class DefText(name: String, source: String) derives Codec.AsObject

/** The knowledge base as data, from the Scala definitions and the checks, without decisions: what
  * `check` writes to `.frflow/kb.json`, and what the ledger's review reads.
  */
final case class Snapshot(
    name: String,
    nodes: List[SnapNode],
    idea: String = "",
    ideaFile: String = "",
    warnings: List[String] = Nil,
    root: Option[NodeId] = None,
    definitions: List[NodeId] = Nil,
    trusted: List[NodeId] = Nil,
    exportedAt: Instant = Instant.EPOCH,
    opaques: List[OpaqueTerm] = Nil,
    params: List[ParamTerm] = Nil,
    types: List[TypeText] = Nil,
    defs: List[DefText] = Nil
) derives Codec.AsObject
