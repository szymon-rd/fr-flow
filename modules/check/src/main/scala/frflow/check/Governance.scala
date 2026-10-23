package frflow
package check

import frflow.ledger.{Decisions, Signing}
import frflow.lean.ObligationName
import frflow.protocol.{NodeKind as _, *}
import java.nio.file.Path

/** What `status` warns of, besides decisions and proofs: the record, the code no node governs, the idea's
  * sections no node is decided against, translations nothing cross-checks, nodes that only restate a part.
  */
object Governance:
  /** Everything `status` warns of: the ledger's signatures, the model and the code, and the checks. */
  def warnings(a: Analysis): List[String] = Signing.warnings(a.inputs.keys, a.ledger) ++ codeWarnings(a) ++ uncrossed(a) ++ restated(a)

  /** The warnings the snapshot carries (the ledger's are read live). */
  def snapshotWarnings(a: Analysis): List[String] = codeWarnings(a) ++ uncrossed(a) ++ restated(a)

  /** Warnings about the model and the code. */
  def codeWarnings(a: Analysis): List[String] =
    val kb = a.kb
    val missing = kb.nodes.flatMap(n => n.governs.filter(a.inputs.missing).map(f => s"${n.id} governs $f, which does not exist"))
    // One owner per file: two nodes governing it would each review it as its own.
    val owners = kb.nodes.flatMap(n => a.code(n).toList.flatMap(_.files).map(_ -> n.id)).groupBy(_._1).toList.sortBy(_._1)
      .collect { case (f, ns) if ns.map(_._2).distinct.size > 1 => s"$f is governed by ${ns.map(_._2).distinct.mkString(" and ")}: give it one owner" }
    // A proof file of no node (after a rename or a removal) proves nothing any more.
    val orphans = a.inputs.proofs.keys.toList.filterNot(id => id == "Lemmas" || kb.node(id).isDefined).sorted
      .map(id => s"lean/Proofs/${kb.name}/$id.lean is the proof file of no node: move it with its node's new id (and its namespace), or remove it")
    missing ++ owners ++ ideaCoverage(a) ++ orphans ++
      ungoverned(a).map(f => s"$f is governed by no node: govern it (a design node) or move it")

  /** Sections of the idea no node is decided against, and nodes naming a section the idea does not have. */
  def ideaCoverage(a: Analysis): List[String] =
    val kb = a.kb
    val named = kb.nodes.map(_.ideaSection.trim).filter(_.nonEmpty)
    val sections = Decisions.ideaSections(a.ideaDecided)._2.map(_._1)
    sections.filterNot(h => named.exists(_.equalsIgnoreCase(h)))
      .map(h => s"the section \"$h\" of ${kb.idea} is the concern of no node: name it on the node that states it (idea = \"$h\"), or move it to Not modelled") ++
      kb.nodes.filter(_.ideaSection.trim.nonEmpty).filterNot(n => sections.exists(_.equalsIgnoreCase(n.ideaSection.trim)))
        .map(n => s"${n.id} is decided against the section \"${n.ideaSection}\", which ${kb.idea} does not have")

  /** Source files no node governs, other than the model's own: code that can change unnoticed (see
    * `Inputs.projectSources`).
    */
  def ungoverned(a: Analysis): List[String] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(a.ws.root)
    val governed = a.kb.nodes.flatMap(a.code).flatMap(_.files).map(f => abs(a.ws.root.resolve(f))).toSet ++
      a.kb.modelFiles.map(f => abs(Path.of(f)))
    // The file that puts the knowledge base together (its concerns listed) is the model's too.
    a.inputs.sources.toList.collect { case (p, text) if !governed(p) && !text.contains("KnowledgeBase(\"") => p }
      .map(p => if p.startsWith(root) then root.relativize(p).toString else p.toString).sorted

  /** One-part nodes Lean proves say what their part says (`restates`, with `complete` proven): a node
    * that only restates its part is not a node.
    */
  def restated(a: Analysis): List[String] =
    a.kb.nodes.flatMap(n => a.current(n).toList.filter(_.result(ObligationName.Complete.lean).exists(_.status == ObligationStatus.Proven))
      .flatMap(_.result(ObligationName.Tried(TryKind.Restates).lean)).filter(_.status == ObligationStatus.Restates).map(_.detail))

  /** Formal contracts whose translation no example cross-checks: checked, and none of their examples
    * evaluated in Lean as in Scala.
    */
  def uncrossed(a: Analysis): List[String] =
    a.kb.nodes.filter(c => c.kind == NodeKind.Contract && a.generate.formal(c) && c.cases.nonEmpty).flatMap { c =>
      a.current(c).filter(k => !k.obligations.exists(o => Analysis.isExample(o) && o.status == ObligationStatus.Proven)).map(_ =>
        s"${c.id}: none of its examples is evaluated in Lean, so nothing checks that the Lean means what the Scala does: give its parameters values Lean has (bindTable for a lookup)")
    }

  /** What each invariant does not reach (by the type of what a contract returns), so a gap is seen. */
  def notes(a: Analysis): List[String] =
    val kb = a.kb
    kb.nodes.filter(_.isInvariant).flatMap { i =>
      val out = kb.nodes.filter(c => c.kind == NodeKind.Contract && !kb.inScope(i).contains(c))
      Option.when(out.nonEmpty)(s"${i.id} does not reach ${out.map(c => s"${c.id} (returns ${c.post.flatMap(_.params.lastOption).fold("?")(_._2)})").mkString(", ")}: its rule is about none of what they return")
    }
