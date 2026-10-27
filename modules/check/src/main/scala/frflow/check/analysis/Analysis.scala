package frflow
package check
package analysis

import cats.effect.IO
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*

/** What the checker knows of a FrModel, computed from `Inputs` alone: the Lean, the contents, the checks still current. */
final class Analysis private (val kb: FrModel, val ws: Workspace, val inputs: Inputs, model: Option[Analysis.Model]):
  // What does not depend on the checks: kept when only they change (after a check).
  private val m: Analysis.Model = model.getOrElse(Analysis.Model(this))
  export inputs.{checks, idea, ledger}
  export m.{examples, files, generate, proofs}

  /** The same inputs with other checks recorded: the Lean and the contents are kept. */
  def withChecks(checks: Map[NodeId, NodeCheck]): Analysis = new Analysis(kb, ws, inputs.copy(checks = checks), Some(m))
  def withTests(tests: Map[NodeId, Recorded], counterexamples: Map[NodeId, List[Counterexample]]): Analysis =
    new Analysis(kb, ws, inputs.copy(tests = tests, counterexamples = counterexamples), Some(m))
  def withConsistency(c: Option[Consistency]): Analysis = new Analysis(kb, ws, inputs.copy(consistency = c), Some(m))

  /** The recorded test of a node's code, if still current: what it depends on has not changed since. */
  def tested(n: Node[?]): Option[TestReport] = inputs.tests.get(NodeId(n.id)).filter(_.key == Tests.key(this, n)).map(_.report)

  /** Among two definitions of a term, the one in force: accepted, and not since rejected. */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  def proofOf(n: Node[?]): Option[String] = inputs.proofs.get(n.id)
  def code(n: Node[?]): Option[CodeRef] = inputs.code.get(n.id)
  def content(n: Node[?]): Content = m.contents.getOrElse(n.id, Contents.of(this, n))
  def hash(n: Node[?]): Hash = content(n).hash
  def definition(n: Node[?]): String = inputs.texts.get(n.file).filter(_ => n.at >= 0).fold("")(Contents.definition(_, n.at))

  // Without its `From:` lines: which answers a section comes from moves no node.
  lazy val (ideaDecided, notModelled) = Idea.split(IdeaDecision.withoutSources(idea))
  def ideaOf(n: Node[?]): String =
    Idea.sections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

  def checkHash(n: Node[?]): Hash =
    if kb.isRoot(n) then m.rootHashes.getOrElse(n.id, CheckHash.of(this, n, Nil))
    else m.hashes.getOrElse(n.id, CheckHash.of(this, n, Nil))

  /** The recorded check of a node, if still current. A result that waited, or timed out, is not final: it is checked again. */
  def current(n: Node[?]): Option[NodeCheck] =
    if !generate.formal(n) then None
    else checks.get(NodeId(n.id)).filter(c => c.hash == checkHash(n) && !Analysis.Pending(c.status))

  /** What doing nothing is, when it meets the root (Lean proved it). */
  def idleOf(n: Node[?]): Option[String] =
    current(n).flatMap(_.result(ObligationName.Tried(TryKind.Idle))).filter(_.status == ObligationStatus.Shown).map(_.detail)

  private lazy val splits: Map[String, Option[Split]] = kb.nodes.map(n => n.id -> Splits.of(this, n)).toMap
  def split(n: Node[?]): Option[Split] = splits.getOrElse(n.id, Splits.of(this, n))

  lazy val snapshot: Snapshot = Snapshots.of(this)
  lazy val annotated: Annotated = Annotate(snapshot, ledger)
  lazy val unsigned: List[(NodeId, Decision)] = Signing.unsigned(ledger, inputs.keys, inputs.keyNames)

  /** Everything `status` warns of: the model and the code (the snapshot's), and the ledger's signatures. */
  lazy val warnings: List[String] = snapshot.warnings ++ inputs.keyWarnings ++ Signing.warnings(inputs.keys, ledger, unsigned)

object Analysis:
  def apply(kb: FrModel, ws: Workspace, inputs: Inputs): Analysis = new Analysis(kb, ws, inputs, None)
  def read(kb: FrModel, ws: Workspace, cfg: Config, ledger: JsonStore[Ledger]): IO[Analysis] =
    Inputs.read(kb, ws, cfg, ledger.load).map(Analysis(kb, ws, _))

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
    // Every node's but a root's depends on its own Lean only; a root's on what its `root_impl` composes too.
    lazy val hashes: Map[String, Hash] =
      a.kb.nodes.filter(n => generate.formal(n) && !a.kb.isRoot(n)).map(n => n.id -> CheckHash.of(a, n, Nil)).toMap
    lazy val rootHashes: Map[String, Hash] =
      a.kb.roots.map { r =>
        val composed = CheckHash.composed(a, r).map(c => hashes.getOrElse(c.id, CheckHash.of(a, c, Nil)))
        r.id -> CheckHash.of(a, r, composed)
      }.toMap
    private lazy val runs: Map[String, List[ExampleResult]] = a.kb.nodes.map(n => n.id -> a.kb.exampleResults(n)).toMap
    def examples(n: Node[?]): List[ExampleResult] = runs.getOrElse(n.id, a.kb.exampleResults(n))

  /** Check results that are not final: checked again. */
  val Pending: Set[CheckStatus] = Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)
