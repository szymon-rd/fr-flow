package frflow
package check

import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.{NodeKind as Kind, *}

/** What the checker knows of a knowledge base, computed from what was read (`Inputs`) alone: the Lean,
  * each node's content and hashes, the checks still current, the snapshot. Nothing here reads or writes.
  */
final class Analysis private (val kb: KnowledgeBase, val ws: Workspace, val inputs: Inputs, model: Option[Analysis.Model]):
  // What does not depend on the checks: kept when only they change (after a check).
  private val m: Analysis.Model = model.getOrElse(Analysis.Model(this))

  def ledger: Ledger = inputs.ledger
  def checks: Map[NodeId, NodeCheck] = inputs.checks
  def idea: String = inputs.idea

  /** The same knowledge base, with other inputs (after a decision, say). */
  def withInputs(in: Inputs): Analysis = Analysis(kb, ws, in)

  /** The same knowledge base and inputs, with other checks recorded: the Lean and the contents are kept. */
  def withChecks(checks: Map[NodeId, NodeCheck]): Analysis = new Analysis(kb, ws, inputs.copy(checks = checks), Some(m))

  // ---------------------------------------------------------------------------
  // The Lean
  // ---------------------------------------------------------------------------

  /** The definitions the developer chose (accepted, and not since rejected): among two definitions of a
    * term, the one in force.
    */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  /** The obligations proven by a theorem of their name in the node's proof file: (node, obligation). */
  def proofs: Set[(String, ObligationName)] = m.proofs

  def generate: Generate = m.generate

  /** The generated Lean files, by their path under `lean/`. */
  def files: Map[String, String] = m.files

  /** The generated file at `rel`, or "". */
  def generated(rel: String): String = files.getOrElse(rel, "")

  /** The authored proof file of a node. */
  def proofOf(n: Node[?]): Option[String] = inputs.proofs.get(n.id)

  /** The lemmas the proof files share. */
  def lemmas: Option[String] = inputs.proofs.get("Lemmas")

  /** Nodes whose `complete` has an authored proof. */
  def authored(id: String): Boolean = proofs((id, ObligationName.Complete))

  def isRoot(n: Node[?]): Boolean = kb.root.exists(_ eq n)

  // ---------------------------------------------------------------------------
  // Content: what the developer decides
  // ---------------------------------------------------------------------------

  /** The idea a root is decided against: the idea without its `## Not modelled` section. */
  lazy val ideaDecided: String = Decisions.splitIdea(idea)._1

  /** The `## Not modelled` section of the idea: the limits of the theory. */
  lazy val notModelled: String = Decisions.splitIdea(idea)._2

  /** The section of the idea a node is decided against. */
  def ideaOf(n: Node[?]): String =
    Decisions.ideaSections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

  /** The node as the developer sees it and decides it (see `Contents`). */
  def content(n: Node[?]): Content = m.contents.getOrElse(n.id, Contents.of(this, n))

  def hash(n: Node[?]): Hash = content(n).hash

  /** The source of the top-level definition a node is written in (see `Contents.definition`). */
  def definition(n: Node[?]): String =
    inputs.texts.get(n.file).filter(_ => n.at >= 0).fold("")(Contents.definition(_, n.at))

  /** The nodes a node rests on: its parents, the definitions it uses, and the contracts its code calls
    * (the snapshot's `parents`, `uses` and `relies`, from which the ledger computes each node's chain).
    */
  def restsOn(n: Node[?]): List[Node[?]] =
    (kb.parentsOf(n) ++ kb.definitionsUsed(n, generate.inForce) ++ generate.callees(n)).distinctBy(_.id)

  /** The source files a node governs, with their fingerprint. */
  def code(n: Node[?]): Option[CodeRef] = inputs.code.get(n.id)

  // ---------------------------------------------------------------------------
  // Checks
  // ---------------------------------------------------------------------------

  /** What a check depends on (see `CheckHash`). */
  def checkHash(n: Node[?]): Hash =
    if isRoot(n) then m.rootHash.getOrElse(CheckHash.of(this, n, Nil)) else m.hashes.getOrElse(n.id, CheckHash.of(this, n, Nil))

  /** The recorded check of a node, if still current. A result that waited, or timed out, is not final:
    * it is checked again.
    */
  def current(n: Node[?]): Option[NodeCheck] =
    if !generate.formal(n) then None
    else checks.get(NodeId(n.id)).filter(c => c.hash == checkHash(n) && !Analysis.Pending(c.status))

  /** What doing nothing is, when it meets the root (Lean proved it). */
  def idleOf(n: Node[?]): Option[String] =
    current(n).flatMap(_.result(ObligationName.Tried(TryKind.Idle).lean)).filter(_.status == ObligationStatus.Idle).map(_.detail)

  private lazy val splits: Map[String, Option[Split]] = kb.nodes.map(n => n.id -> Splits.of(this, n)).toMap

  /** How a node's parts make it (see `Splits`). */
  def split(n: Node[?]): Option[Split] = splits.getOrElse(n.id, Splits.of(this, n))

  // ---------------------------------------------------------------------------
  // What agents and the developer read
  // ---------------------------------------------------------------------------

  /** The knowledge base as data, from the Scala definitions and the checks; without decisions. */
  lazy val snapshot: Snapshot = Snapshots.of(this)

  /** The snapshot with the developer's decisions. */
  lazy val annotated: Annotated = Decisions.annotate(snapshot, ledger)

  /** Where the developer stands on a node. */
  def state(n: Node[?]): ReviewState = annotated.byId.get(NodeId(n.id)).fold(ReviewState.Proposed)(_.state)

  def gone: List[NodeId] = annotated.gone.map(_.id)

object Analysis:
  def apply(kb: KnowledgeBase, ws: Workspace, inputs: Inputs): Analysis = new Analysis(kb, ws, inputs, None)

  /** What an analysis computes that does not depend on the checks recorded. */
  private final class Model(a: Analysis):
    lazy val proofs: Set[(String, ObligationName)] =
      val base = Generate(a.kb)
      a.kb.nodes.flatMap { n =>
        val names = base.obligations(n).map(_.name).toSet + ObligationName.Feasible
        a.proofOf(n).toList.flatMap(src => LeanSource.theorems(src).flatMap(t => ObligationName.parse(t.name)).filter(names).map(n.id -> _))
      }.toSet
    lazy val generate: Generate = Generate(a.kb, proofs, a.chosen)
    lazy val files: Map[String, String] = generate.files
    lazy val contents: Map[String, Content] = a.kb.nodes.map(n => n.id -> Contents.of(a, n)).toMap
    // Every node's but the root's depends on its own Lean only; the root's on what `root_impl` composes too.
    lazy val hashes: Map[String, Hash] =
      a.kb.nodes.filter(n => generate.formal(n) && !a.isRoot(n)).map(n => n.id -> CheckHash.of(a, n, Nil)).toMap
    lazy val rootHash: Option[Hash] =
      a.kb.root.map(r => CheckHash.of(a, r, CheckHash.composed(a, r).map(c => hashes.getOrElse(c.id, CheckHash.of(a, c, Nil)))))

  /** Check results that are not final: checked again. */
  val Pending: Set[CheckStatus] = Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)

  /** An example of the contract, evaluated in Lean (not a probe, nor its code's run). */
  def isExample(r: Result): Boolean = ObligationName.parse(r.name).exists { case ObligationName.Eval(_) => true; case _ => false }

  /** A node's kind, as the snapshot names it. */
  def kindOf(n: Node[?]): Kind = Kind.valueOf(n.kind.toString)

  /** A node's kind as people read it: an invariant is a claim with a rule. */
  def shownKind(n: Node[?]): String = kindOf(n).shown(n.isInvariant)
