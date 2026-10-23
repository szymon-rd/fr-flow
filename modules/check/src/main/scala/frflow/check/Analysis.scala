package frflow
package check

import cats.effect.IO
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*

/** What the checker knows of a knowledge base, computed from what was read (`Inputs`) alone: the Lean,
  * each node's content and hashes, the checks still current, the snapshot. Nothing here reads or writes.
  */
final class Analysis private (val kb: KnowledgeBase, val ws: Workspace, val inputs: Inputs, model: Option[Analysis.Model]):
  // What does not depend on the checks: kept when only they change (after a check).
  private val m: Analysis.Model = model.getOrElse(Analysis.Model(this))
  export inputs.{checks, idea, ledger}
  export m.{examples, files, generate, proofs}

  /** The same knowledge base and inputs, with other checks recorded: the Lean and the contents are kept. */
  def withChecks(checks: Map[NodeId, NodeCheck]): Analysis = new Analysis(kb, ws, inputs.copy(checks = checks), Some(m))

  /** The definitions the developer chose (accepted, and not since rejected): among two definitions of a
    * term, the one in force.
    */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  /** The authored proof file of a node. */
  def proofOf(n: Node[?]): Option[String] = inputs.proofs.get(n.id)

  /** The idea a root is decided against, and its `## Not modelled` section: the limits of the theory. */
  lazy val (ideaDecided, notModelled) = Idea.split(idea)

  /** The section of the idea a node is decided against. */
  def ideaOf(n: Node[?]): String =
    Idea.sections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

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

  /** What a check depends on (see `CheckHash`). */
  def checkHash(n: Node[?]): Hash =
    if kb.isRoot(n) then m.rootHash.getOrElse(CheckHash.of(this, n, Nil)) else m.hashes.getOrElse(n.id, CheckHash.of(this, n, Nil))

  /** The recorded check of a node, if still current. A result that waited, or timed out, is not final:
    * it is checked again.
    */
  def current(n: Node[?]): Option[NodeCheck] =
    if !generate.formal(n) then None
    else checks.get(NodeId(n.id)).filter(c => c.hash == checkHash(n) && !Analysis.Pending(c.status))

  /** What doing nothing is, when it meets the root (Lean proved it). */
  def idleOf(n: Node[?]): Option[String] =
    current(n).flatMap(_.result(ObligationName.Tried(TryKind.Idle))).filter(_.status == ObligationStatus.Shown).map(_.detail)

  private lazy val splits: Map[String, Option[Split]] = kb.nodes.map(n => n.id -> Splits.of(this, n)).toMap

  /** How a node's parts make it (see `Splits`). */
  def split(n: Node[?]): Option[Split] = splits.getOrElse(n.id, Splits.of(this, n))

  /** The knowledge base as data, from the Scala definitions and the checks; without decisions. */
  lazy val snapshot: Snapshot = Snapshots.of(this)

  /** The snapshot with the developer's decisions. */
  lazy val annotated: Annotated = Annotate(snapshot, ledger)

  /** The decisions not signed by one of the project's keys. */
  lazy val unsigned: List[(NodeId, Decision)] = Signing.unsigned(ledger, inputs.keys)

  /** Everything `status` warns of: the model and the code (the snapshot's), and the ledger's signatures. */
  lazy val warnings: List[String] = snapshot.warnings ++ Signing.warnings(inputs.keys, ledger, unsigned)

object Analysis:
  def apply(kb: KnowledgeBase, ws: Workspace, inputs: Inputs): Analysis = new Analysis(kb, ws, inputs, None)

  /** The workspace as it is now, analysed. */
  def read(kb: KnowledgeBase, ws: Workspace, cfg: Config, ledger: JsonStore[Ledger]): IO[Analysis] =
    Inputs.read(kb, ws, cfg, ledger.load).map(Analysis(kb, ws, _))

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
      a.kb.nodes.filter(n => generate.formal(n) && !a.kb.isRoot(n)).map(n => n.id -> CheckHash.of(a, n, Nil)).toMap
    lazy val rootHash: Option[Hash] =
      a.kb.root.map(r => CheckHash.of(a, r, CheckHash.composed(a, r).map(c => hashes.getOrElse(c.id, CheckHash.of(a, c, Nil)))))
    private lazy val runs: Map[String, List[ExampleResult]] = a.kb.nodes.map(n => n.id -> a.kb.exampleResults(n)).toMap
    /** The results of a node's examples (see `KnowledgeBase.exampleResults`): run once. */
    def examples(n: Node[?]): List[ExampleResult] = runs.getOrElse(n.id, a.kb.exampleResults(n))

  /** Check results that are not final: checked again. */
  val Pending: Set[CheckStatus] = Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)

  /** An example of the contract, evaluated in Lean (not a probe, nor its code's run). */
  def isExample(r: Result): Boolean = r.name match
    case ObligationName.Eval(_) => true
    case _ => false
