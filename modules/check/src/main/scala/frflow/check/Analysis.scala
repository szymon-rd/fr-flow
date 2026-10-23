package frflow
package check

import cats.effect.IO
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*
import frflow.protocol.ObligationName.{Complete, Feasible, Tried}
import frflow.protocol.ObligationStatus.*
import io.circe.Json

/** What the checker knows of a knowledge base, computed from `Inputs` alone: the Lean, the contents, the checks still current. */
final class Analysis private (val kb: KnowledgeBase, val ws: Workspace, val inputs: Inputs, model: Option[Analysis.Model]):
  // What does not depend on the checks: kept when only they change (after a check).
  private val m: Analysis.Model = model.getOrElse(Analysis.Model(this))
  export inputs.{checks, idea, ledger}
  export m.{examples, files, generate, proofs}

  /** The same inputs with other checks recorded: the Lean and the contents are kept. */
  def withChecks(checks: Map[NodeId, NodeCheck]): Analysis = new Analysis(kb, ws, inputs.copy(checks = checks), Some(m))

  /** Among two definitions of a term, the one in force: accepted, and not since rejected. */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  def proofOf(n: Node[?]): Option[String] = inputs.proofs.get(n.id)
  def code(n: Node[?]): Option[CodeRef] = inputs.code.get(n.id)
  def content(n: Node[?]): Content = m.contents.getOrElse(n.id, Contents.of(this, n))
  def hash(n: Node[?]): Hash = content(n).hash
  def definition(n: Node[?]): String = inputs.texts.get(n.file).filter(_ => n.at >= 0).fold("")(Contents.definition(_, n.at))

  lazy val (ideaDecided, notModelled) = Idea.split(idea)
  def ideaOf(n: Node[?]): String =
    Idea.sections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

  def checkHash(n: Node[?]): Hash =
    if kb.isRoot(n) then m.rootHash.getOrElse(CheckHash.of(this, n, Nil)) else m.hashes.getOrElse(n.id, CheckHash.of(this, n, Nil))

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
  lazy val unsigned: List[(NodeId, Decision)] = Signing.unsigned(ledger, inputs.keys)

  /** Everything `status` warns of: the model and the code (the snapshot's), and the ledger's signatures. */
  lazy val warnings: List[String] = snapshot.warnings ++ Signing.warnings(inputs.keys, ledger, unsigned)

object Analysis:
  def apply(kb: KnowledgeBase, ws: Workspace, inputs: Inputs): Analysis = new Analysis(kb, ws, inputs, None)
  def read(kb: KnowledgeBase, ws: Workspace, cfg: Config, ledger: JsonStore[Ledger]): IO[Analysis] =
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
    // Every node's but the root's depends on its own Lean only; the root's on what `root_impl` composes too.
    lazy val hashes: Map[String, Hash] =
      a.kb.nodes.filter(n => generate.formal(n) && !a.kb.isRoot(n)).map(n => n.id -> CheckHash.of(a, n, Nil)).toMap
    lazy val rootHash: Option[Hash] =
      a.kb.root.map(r => CheckHash.of(a, r, CheckHash.composed(a, r).map(c => hashes.getOrElse(c.id, CheckHash.of(a, c, Nil)))))
    private lazy val runs: Map[String, List[ExampleResult]] = a.kb.nodes.map(n => n.id -> a.kb.exampleResults(n)).toMap
    def examples(n: Node[?]): List[ExampleResult] = runs.getOrElse(n.id, a.kb.exampleResults(n))

  /** Check results that are not final: checked again. */
  val Pending: Set[CheckStatus] = Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)

/** A node as the developer sees it and decides it: a decision is bound to its hash, its parts too (docs/DAG.md §5). */
object Contents:
  private def str(s: String): Json = Json.fromString(s)
  private def strs(xs: Seq[String]): Json = Json.fromValues(xs.map(Json.fromString))

  def of(a: Analysis, n: Node[?]): Content =
    val kb = a.kb
    val implementation = kb.implementation(n).flatMap { i =>
      // A flow is decided as Lean reads it: its Scala is a `def` elsewhere, governed by a design decision.
      val proven = i.proven.toList.flatMap(d => s"proven: ${d.name}" +: Def.closure(List(d))
        .map(x => s"${x.name} = ${if x.isFlow then x.lifted.lean else x.lifted.source}"))
      val runs = Option.when(i.wiring.nonEmpty)(if i.proven.isDefined then s"runs: ${i.wiring}" else i.wiring).toList
      Option.when((proven ++ runs).nonEmpty)((proven ++ runs).mkString("\n"))
    }
    // The root is decided against the idea's title and lead; a node naming a section, against that section.
    val idea =
      if n.ideaSection.nonEmpty then Seq("idea" -> str(a.ideaOf(n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(a.notModelled))
      else if kb.isRoot(n) then Seq("idea" -> str(Idea.sections(a.ideaDecided)._1), "notModelled" -> str(a.notModelled))
      else Nil
    val terms = kb.termsOf(n).toSet ++ n.defines
    val vocabulary = (kb.opaques.filter(o => terms(o.name)).map(o => s"${o.name}: ${o.means}") ++
      kb.params.filter(p => terms(p.name)).map(p => s"${p.name}: ${p.means}")).sorted
    val sources = Seq("formula" -> n.formula, "post" -> n.post, "rule" -> n.rule, "check" -> n.local)
      .collect { case (k, Some(l)) => k -> str(l.source) }
    // The fields in this order: the order is part of the hash, so a change of it reviews every node again.
    Content((List(
      Some("kind" -> str(n.kind.toString)),
      Some("parents" -> strs(n.parents.map(_.id))),
      Option.when(kb.isStatement(n))("parts" -> strs(kb.parts(n).map(_.id))),
      Some("statement" -> str(n.statement)),
      Some("why" -> str(n.why)),
      Some("sources" -> Json.obj(sources*)),
      Some("substitutions" -> strs(n.substs.map(s => s"${s.name} := ${s.term.fold(s.lean)(_.source)}"))),
      Some("examples" -> strs(n.cases.map(_.describe))),
      Some("vocabulary" -> strs(vocabulary)),
      Some("uses" -> strs(a.generate.sourcesUsedBy(n))),
      Some("governs" -> strs(n.governs)),
      Some("definition" -> str(a.definition(n))),
      n.op.map(o => "op" -> str(o.name)),
      n.replaced.map(r => "replaces" -> str(r.id)),
      Option.when(n.kept.nonEmpty)("keeps" -> strs(n.kept.map(_.describe))),
      Option.when(n.expected.nonEmpty)("expects" -> strs(n.expected.map((st, l) => s"$st: ${l.source}"))),
      implementation.map("implementation" -> str(_)),
      n.modelOf.map(mo => "model" -> strs(a.generate.boundaryModules.modelText(mo)))
    ).flatten ++ idea)*)

  private val Statement = """^\s*(?:(?:private|protected|final|lazy|override|inline)\s+)*(?:val|def|given|var)\b.*""".r

  /** The top-level definition at `at`, with every call chained on it: what is decided is what is written, nothing hidden. */
  def definition(text: String, at: Int): String =
    val lines = text.split("\n", -1).toList
    val starts = lines.scanLeft(0)(_ + _.length + 1)
    val k = starts.lastIndexWhere(_ <= at).min(lines.size - 1).max(0)
    def indent(l: String) = l.takeWhile(_ == ' ').length
    def comment(t: String) = Seq("//", "/*", "*").exists(t.startsWith)
    // The statement holding the call: the nearest `val`/`def` above it, no deeper than its line...
    val from = (k to 0 by -1).find(j => lines(j).trim.nonEmpty && indent(lines(j)) <= indent(lines(k)) && Statement.matches(lines(j))).getOrElse(k)
    // ...to the next line as shallow as it that does not continue it (a closing bracket, a chained call;
    // a comment may sit between chained calls, and the comments before the next statement are not its).
    val to = ((from + 1) until lines.size).find { j =>
      val t = lines(j).trim
      t.nonEmpty && !comment(t) && indent(lines(j)) <= indent(lines(from)) && !Seq(")", "}", "]", ".").exists(t.startsWith)
    }.getOrElse(lines.size)
    val body = lines.slice(from, to).map(_.stripTrailing).reverse.dropWhile(l => l.isEmpty || comment(l.trim)).reverse
    // Dedented: moving the statement into or out of a block is not a change of what it says.
    val margin = body.filter(_.trim.nonEmpty).map(indent).minOption.getOrElse(0)
    body.map(_.drop(margin)).mkString("\n")

/** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. */
object CheckHash:
  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 7

  /** What `root_impl` composes: every proof and every implementation. */
  def composed(a: Analysis, root: Node[?]): List[Node[?]] =
    val g = a.generate
    (g.trusted ++ a.kb.nodes.filter(c => g.provenImpl(c).isDefined) ++ a.kb.nodes.filter(g.formal)).distinctBy(_.id).filterNot(_ eq root)

  /** The hash of a node's check, given the hashes of what it composes (the root's; none for another node). */
  def of(a: Analysis, n: Node[?], composed: List[Hash]): Hash =
    val g = a.generate
    val kb = a.kb
    val proof = a.proofOf(n)
    val lemmas = proof.filter(LeanSource.lemmaImports(_).nonEmpty).flatMap(_ => a.inputs.proofs.get("Lemmas")).getOrElse("")
    // The specs of other nodes a proof imports: a change to them re-checks it.
    val imported = proof.fold("")(src => s"(?m)^\\s*import\\s+FrFlowGen\\.${java.util.regex.Pattern.quote(kb.name)}\\.(\\w+)\\.Spec".r
      .findAllMatchIn(src).map(_.group(1)).filter(_ != n.id).flatMap(kb.node).filter(g.formal).map(g.spec).mkString)
    // A node's proofs read its parts' and callees' statements (and its parts' `holds`, over the leaves below them),
    // not how those are proven or coded: a change of code below re-checks only the contract and `root_impl`.
    val below = (kb.parts(n) ++ g.callees(n)).filter(g.formal).distinctBy(_.id).filterNot(_ eq n).map(g.spec).mkString
    val partsHold = kb.parts(n).filter(g.formal).filterNot(_ eq n).map(g.holdsStatement).mkString
    Hash(Sha.parts((Seq(g.spec(n), g.auto(n), g.theorems(n), g.checks(n), g.evalFile(n).getOrElse(""),
      g.provenImpl(n).fold("")(_ => g.impl(n)), if kb.isRoot(n) then g.rootImpl.fold("")(_._2) else "",
      proof.getOrElse(""), lemmas, imported, below, partsHold, composed.map(_.value).mkString,
      CheckerVersion.toString) ++ g.declarationsUsedBy(n))*))

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`; none for a node with no parts. */
object Splits:
  def of(a: Analysis, n: Node[?]): Option[Split] =
    val parts = a.kb.parts(n)
    def all(o: Outcome) = Split(o, parts.map(p => Split.Part(NodeId(p.id), o.status, o.detail)), o)
    if parts.isEmpty || !a.kb.isStatement(n) then None
    else Some(a.current(n).fold(all(notCurrent(a.checks.get(NodeId(n.id)))))(checked(parts, _)))

  private def notCurrent(c: Option[NodeCheck]): Outcome =
    val why = c.filter(_.status == CheckStatus.Waiting).flatMap(_.messages.headOption)
      .orElse(c.filter(_.status == CheckStatus.Timeout).map(_ => "Lean timed out: run check again"))
      .getOrElse(if c.isDefined then "changed since the last check" else "not checked yet")
    c.map(_.status) match
      case Some(CheckStatus.Timeout) => Outcome(Timeout, why)
      case Some(CheckStatus.ModelError) => Outcome(Failed, "the model does not build: " + c.flatMap(_.messages.headOption).getOrElse(""))
      case _ => Outcome(Unchecked, why)

  private def checked(parts: List[Node[?]], c: NodeCheck): Split =
    val complete = c.result(Complete) match
      case Some(r) if r.status == Proven && c.obligations.exists(o => o.name == Feasible && o.status != Proven) =>
        Outcome(Open, "its parts make it by an authored proof: prove `feasible` too (some world meets the parts), or give a proven implementation below")
      case Some(r) => Outcome(r.status, r.detail.linesIterator.nextOption().getOrElse(""))
      case None => Outcome(Failed, c.messages.headOption.getOrElse("the check failed"))
    val needed = parts.map(p => c.result(Tried(if parts.size == 1 then TryKind.Vacuous else TryKind.Needed(p.id)))
      .fold(Split.Part(NodeId(p.id), Unchecked, "not checked"))(r => Split.Part(NodeId(p.id), r.status, r.detail)))
    Split(complete, needed, c.result(Tried(TryKind.Clash)).fold(Outcome(Unchecked, "not checked"))(Outcome.of))
