package frflow.protocol

import io.circe.{Codec, Decoder, Encoder}
import java.time.Instant

/** What Lean is asked about a node; `lean` names its theorem, and the result recorded. */
enum ObligationName:
  case Complete, Feasible, Impl, Check
  case Cover(invariant: String)
  case Expect(i: Int)
  case Tried(kind: TryKind)
  /** Example `i` (probe `j`: an input near the examples'), of the contract and of its proven code. */
  case Eval(i: Int)
  case EvalImpl(i: Int)
  case Probe(j: Int)
  case ProbeImpl(j: Int)
  case RootImpl

  def lean: String = this match
    case Complete     => "complete"
    case Feasible     => "feasible"
    case Impl         => "impl"
    case Check        => "check"
    case Cover(i)     => s"cover_$i"
    case Expect(i)    => s"expect_$i"
    case Tried(k)     => ObligationName.tryName(k)
    case Eval(i)      => s"eval_$i"
    case EvalImpl(i)  => s"evalImpl_$i"
    case Probe(j)     => s"probe_$j"
    case ProbeImpl(j) => s"probeImpl_$j"
    case RootImpl     => "root_impl"

  override def toString: String = lean
  def isProbe: Boolean = PartialFunction.cond(this) { case Probe(_) | ProbeImpl(_) => true }
  /** An example or a probe, evaluated in Lean: the translation's cross-check. */
  def isEvaluation: Boolean = isProbe || PartialFunction.cond(this) { case Eval(_) | EvalImpl(_) => true }

  /** The same evaluation, of the proven code instead of the contract. */
  def ofCode: ObligationName = this match
    case Eval(i)  => EvalImpl(i)
    case Probe(j) => ProbeImpl(j)
    case other    => other

object ObligationName:
  private def tryName(k: TryKind): String = k match
    case TryKind.Needed(part)     => s"needed_$part"
    case TryKind.Vacuous          => "vacuous"
    case TryKind.Restates         => "restates"
    case TryKind.Clash            => "clash"
    case TryKind.Unsat            => "unsat"
    case TryKind.Idle             => "idle"
    case TryKind.VacuousExpect(i) => s"vacuous_expect_$i"
    case TryKind.RestatesConjunct(p, i) => s"restates_${i}_$p"

  private val fixed: Map[String, ObligationName] =
    (List(Complete, Feasible, Impl, Check, RootImpl) ++
      List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle).map(Tried(_))).map(o => o.lean -> o).toMap
  private val indexed: Map[String, Int => ObligationName] = Map("expect" -> Expect.apply, "eval" -> Eval.apply,
    "vacuous_expect" -> (i => Tried(TryKind.VacuousExpect(i))), "evalImpl" -> EvalImpl.apply, "probe" -> Probe.apply, "probeImpl" -> ProbeImpl.apply)
  private val Indexed = s"(${indexed.keys.mkString("|")})_(\\d{1,9})".r
  private val OfNode = """(cover|needed)_(.+)""".r
  private val Conjunct = """restates_(\d{1,9})_(.+)""".r

  def parse(s: String): Option[ObligationName] = fixed.get(s).orElse(s match
    case Indexed(kind, i)    => indexed.get(kind).map(_(i.toInt))
    case Conjunct(i, id)     => Some(Tried(TryKind.RestatesConjunct(id, i.toInt)))
    case OfNode("cover", id) => Some(Cover(id))
    case OfNode(_, id)       => Some(Tried(TryKind.Needed(id)))
    case _                   => None)

  given Codec[ObligationName] = Codec.from(
    Decoder.decodeString.emap(s => parse(s).toRight(s"unknown obligation $s")), Encoder.encodeString.contramap(_.lean))

final case class Result(name: ObligationName, status: ObligationStatus, detail: String = "") derives Codec.AsObject:
  def isEvaluation: Boolean = name.isEvaluation
  /** Nothing to do about it: an obligation proven, a try that shows nothing wrong, or a limit of what the
    * node says (doing nothing meets the root, or the node says what its one part says, or a part one of its conjuncts).
    */
  def fine: Boolean = status.fine || PartialFunction.cond(name) {
    case ObligationName.Tried(TryKind.Idle | TryKind.Restates | TryKind.RestatesConjunct(_, _)) => true
  }

/** The outcome of checking one node, against the hash of what the check depends on. */
final case class NodeCheck(hash: Hash, status: CheckStatus, obligations: List[Result], messages: List[String],
    axioms: List[String], at: Instant, hint: Option[String] = None) derives Codec.AsObject:
  def result(name: ObligationName): Option[Result] = obligations.find(_.name == name)

final case class Outcome(status: ObligationStatus, detail: String = "") derives Codec.AsObject
object Outcome:
  val unchecked: Outcome = Outcome(ObligationStatus.Unchecked, "not checked yet")
  def of(r: Result): Outcome = Outcome(r.status, r.detail)

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`. */
final case class Split(complete: Outcome, needed: List[Split.Part], clash: Outcome) derives Codec.AsObject:
  def proven: Boolean = complete.status == ObligationStatus.Proven && needed.forall(_.status.fine) && clash.status.fine
object Split:
  final case class Part(id: NodeId, status: ObligationStatus, detail: String) derives Codec.AsObject

/** An example of a contract: what fails of it in Scala, and what Lean computes of it. */
final case class ExampleView(note: String, `given`: List[String], call: String, expected: Boolean, fails: Option[String],
    codeFails: Option[String], lean: Option[Outcome], leanImplementation: Option[Outcome]) derives Codec.AsObject:
  def passes: Boolean = fails.isEmpty && codeFails.isEmpty

final case class CodeRef(files: List[String], fingerprint: Fingerprint) derives Codec.AsObject
final case class Kept(id: NodeId, view: String, rule: String, status: ObligationStatus, detail: String) derives Codec.AsObject
final case class Expectation(statement: String, source: String, status: ObligationStatus, detail: String) derives Codec.AsObject
final case class ImplProof(name: String, status: ObligationStatus, detail: String) derives Codec.AsObject
final case class ObligationText(name: String, statement: String, description: String) derives Codec.AsObject
final case class ProofFile(file: String, source: String) derives Codec.AsObject

/** One node of the snapshot: what the developer decides (`content`, `hash`), and what the checks found. A
  * `leaf` is a claim nothing below proves (a hypothesis of root_impl).
  */
final case class SnapNode(id: NodeId, kind: NodeKind, content: Content, hash: Hash, parents: List[NodeId] = Nil,
    parts: List[NodeId] = Nil, replaces: Option[NodeId] = None, op: Option[String] = None, defines: List[String] = Nil,
    uses: List[NodeId] = Nil, relies: List[NodeId] = Nil, rule: Boolean = false, idle: Option[String] = None,
    status: Option[CheckStatus] = None, leaf: Boolean = false, examples: List[ExampleView] = Nil, code: Option[CodeRef] = None,
    split: Option[Split] = None, invariants: List[Kept] = Nil, expectations: List[Expectation] = Nil,
    implementationProof: Option[ImplProof] = None, rootImpl: Option[Outcome] = None, covers: List[NodeId] = Nil,
    exempts: List[NodeId] = Nil, obligations: List[ObligationText] = Nil, proof: Option[ProofFile] = None,
    holds: String = "", lean: String = "", messages: List[String] = Nil) derives Codec.AsObject:
  def shownKind: String = kind.shown(rule)
  def examplesPassing: (Int, Int) = (examples.count(_.passes), examples.size)

final case class OpaqueTerm(name: String, means: String, definedBy: Option[NodeId]) derives Codec.AsObject
final case class ParamTerm(name: String, means: String, operation: Boolean, definedBy: Option[NodeId], lean: String) derives Codec.AsObject
final case class TypeText(name: String, lean: String) derives Codec.AsObject
final case class DefText(name: String, source: String) derives Codec.AsObject

/** The knowledge base as data, without decisions: what `check` writes to `.frflow/kb.json`. */
final case class Snapshot(name: String, nodes: List[SnapNode], idea: String = "", ideaFile: String = "",
    warnings: List[String] = Nil, root: Option[NodeId] = None, definitions: List[NodeId] = Nil, trusted: List[NodeId] = Nil,
    exportedAt: Instant = Instant.EPOCH, opaques: List[OpaqueTerm] = Nil, params: List[ParamTerm] = Nil,
    types: List[TypeText] = Nil, defs: List[DefText] = Nil) derives Codec.AsObject
