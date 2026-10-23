package frflow
package check

import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.{NodeKind as Kind, *}

/** What the checker knows of a knowledge base, computed from what was read (`Inputs`) alone: the Lean,
  * each node's content and hashes, the checks still current, the snapshot. Nothing here reads or writes.
  */
final class Analysis(val kb: KnowledgeBase, val ws: Workspace, val inputs: Inputs):

  def ledger: Ledger = inputs.ledger
  def checks: Map[NodeId, NodeCheck] = inputs.checks
  def idea: String = inputs.idea

  /** The same knowledge base, with other inputs (after a check, or a decision). */
  def withInputs(in: Inputs): Analysis = Analysis(kb, ws, in)

  // ---------------------------------------------------------------------------
  // The Lean
  // ---------------------------------------------------------------------------

  /** The definitions the developer chose (accepted, and not since rejected): among two definitions of a
    * term, the one in force.
    */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  /** The obligations proven by a theorem of their name in the node's proof file: (node, obligation). */
  lazy val proofs: Set[(String, String)] =
    val base = Generate(kb)
    kb.nodes.flatMap { n =>
      val names = base.obligations(n).map(_.name).toSet + "feasible"
      proofOf(n).toList.flatMap(src => Lean.theorems(src).map(_.name).filter(names).map(n.id -> _))
    }.toSet

  lazy val generate: Generate = Generate(kb, proofs, chosen)

  /** The generated Lean files, by their path under `lean/`. */
  lazy val files: Map[String, String] = generate.files

  /** The generated file at `rel`, or "". */
  def generated(rel: String): String = files.getOrElse(rel, "")

  /** The authored proof file of a node. */
  def proofOf(n: Node[?]): Option[String] = inputs.proofs.get(n.id)

  /** The lemmas the proof files share. */
  def lemmas: Option[String] = inputs.proofs.get("Lemmas")

  /** Nodes whose `complete` has an authored proof. */
  def authored(id: String): Boolean = proofs((id, "complete"))

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

  private lazy val contents: Map[String, Content] = kb.nodes.map(n => n.id -> Contents.of(this, n)).toMap

  /** The node as the developer sees it and decides it (see `Contents`). */
  def content(n: Node[?]): Content = contents.getOrElse(n.id, Contents.of(this, n))

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

  // Every node's but the root's depends on its own Lean only; the root's on what `root_impl` composes too.
  private lazy val hashes: Map[String, Hash] =
    kb.nodes.filter(n => generate.formal(n) && !isRoot(n)).map(n => n.id -> CheckHash.of(this, n, Nil)).toMap
  private lazy val rootHash: Option[Hash] =
    kb.root.map(r => CheckHash.of(this, r, CheckHash.composed(this, r).map(c => hashes.getOrElse(c.id, CheckHash.of(this, c, Nil)))))

  /** What a check depends on (see `CheckHash`). */
  def checkHash(n: Node[?]): Hash =
    if isRoot(n) then rootHash.getOrElse(CheckHash.of(this, n, Nil)) else hashes.getOrElse(n.id, CheckHash.of(this, n, Nil))

  /** The recorded check of a node, if still current. A result that waited, or timed out, is not final:
    * it is checked again.
    */
  def current(n: Node[?]): Option[NodeCheck] =
    if !generate.formal(n) then None
    else checks.get(NodeId(n.id)).filter(c => c.hash == checkHash(n) && !Analysis.Pending(c.status))

  /** What doing nothing is, when it meets the root (Lean proved it). */
  def idleOf(n: Node[?]): Option[String] =
    current(n).flatMap(_.result("idle")).filter(_.status == ObligationStatus.Idle).map(_.detail)

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
  /** Check results that are not final: checked again. */
  val Pending: Set[CheckStatus] = Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)

  /** A node's kind, as the snapshot names it. */
  def kindOf(n: Node[?]): Kind = Kind.valueOf(n.kind.toString)

  /** A node's kind as people read it: an invariant is a claim with a rule. */
  def shownKind(n: Node[?]): String = kindOf(n).shown(n.isInvariant)
