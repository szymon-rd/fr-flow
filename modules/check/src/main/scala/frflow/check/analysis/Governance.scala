package frflow
package check
package analysis

import frflow.ledger.Idea
import frflow.protocol.*
import frflow.protocol.ObligationName.Eval
import frflow.protocol.ObligationStatus.*
import java.nio.file.Path

/** What `status` warns of besides decisions, proofs and signatures (the snapshot carries these; the ledger's are read live). */
object Governance:
  /** None before the first node: while the idea is being written, there is nothing to cover it or to govern files yet. */
  def warnings(a: Analysis): List[String] = if a.kb.nodes.isEmpty then Nil else ofNodes(a)

  private def ofNodes(a: Analysis): List[String] =
    val kb = a.kb
    val missing = kb.nodes.flatMap(n => n.governs.filter(a.inputs.missing).map(f => s"${n.id} governs $f, which does not exist"))
    // One owner per file: two nodes governing it would each review it as its own.
    val owners = kb.nodes.flatMap(n => a.code(n).toList.flatMap(_.files).map(_ -> n.id)).groupBy(_._1).toList.sortBy(_._1)
      .collect { case (f, ns) if ns.map(_._2).distinct.size > 1 => s"$f is governed by ${ns.map(_._2).distinct.mkString(" and ")}: give it one owner" }
    val named = kb.nodes.map(_.ideaSection.trim).filter(_.nonEmpty)
    val sections = Idea.sections(a.ideaDecided)._2.map(_._1)
    val ideaCoverage = sections.filterNot(h => named.exists(_.equalsIgnoreCase(h)))
      .map(h => s"the section \"$h\" of ${kb.idea} is the concern of no node: name it on the node that states it (idea = \"$h\"), or move it to Not modelled") ++
      kb.nodes.filter(_.ideaSection.trim.nonEmpty).filterNot(n => sections.exists(_.equalsIgnoreCase(n.ideaSection.trim)))
        .map(n => s"${n.id} is decided against the section \"${n.ideaSection}\", which ${kb.idea} does not have")
    // A proof file of no node (after a rename or a removal) proves nothing any more.
    val orphans = a.inputs.proofs.keys.toList.filterNot(id => id == "Lemmas" || kb.node(id).isDefined).sorted
      .map(id => s"lean/Proofs/${kb.name}/$id.lean is the proof file of no node: move it with its node's new id (and its namespace), or remove it")
    // Formal contracts whose translation no example cross-checks: checked, and none of their examples evaluated in Lean,
    // unless only because an operation they run is plain code (tested against its own contract): Lean has no value for it,
    // and no binding can give one; the node's line in check says so.
    val uncrossed = kb.nodes.filter(c => c.kind == NodeKind.Contract && c.cases.nonEmpty).flatMap { c =>
      def isEval(o: Result) = PartialFunction.cond(o.name) { case Eval(_) => true }
      def plainCode(o: Result) = o.status == Unevaluated && o.detail.endsWith(frflow.lean.obligation.Evals.NoDefine)
      a.current(c).filter { r =>
        val evals = r.obligations.filter(isEval)
        !evals.exists(_.status == Proven) && !(evals.nonEmpty && evals.forall(plainCode))
      }.map(_ =>
        s"${c.id}: none of its examples is evaluated in Lean, so nothing checks that the Lean means what the Scala does: " +
          "give its parameters values Lean has (bindTable for a lookup)")
    }
    // A one-part node Lean proves equivalent to its part (`complete` and `restates` both proven) says nothing of its own;
    // a part Lean proves equivalent to one conjunct of its parent says nothing the parent does not.
    val restated = kb.nodes.flatMap(n => a.current(n).toList.flatMap { c =>
      c.result(ObligationName.Tried(TryKind.Restates)).filter(r => r.status == Shown && c.result(ObligationName.Complete).exists(_.status == Proven)) ++
        c.obligations.filter(r => r.status == Shown && PartialFunction.cond(r.name) { case ObligationName.Tried(TryKind.RestatesConjunct(_, _)) => true })
    }.map(_.detail))
    missing ++ owners ++ ideaCoverage ++ orphans ++ ungoverned(a).map(f => s"$f is governed by no node: govern it (a design node) or move it") ++
      uncrossed ++ restated

  /** Source files no node governs, other than the model's own: code that can change unnoticed (see `Inputs.projectSources`). */
  def ungoverned(a: Analysis): List[String] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(a.ws.root)
    val governed = a.kb.nodes.flatMap(a.code).flatMap(_.files).map(f => abs(a.ws.root.resolve(f))).toSet ++
      a.kb.modelFiles.map(f => abs(Path.of(f)))
    // The file that puts the knowledge base together (its concerns listed) is the model's too.
    a.inputs.sources.toList.collect { case (p, text) if !governed(p) && !text.contains("KnowledgeBase(\"") => p }
      .map(p => if p.startsWith(root) then root.relativize(p).toString else p.toString).sorted
