package frflow
package check

import frflow.ledger.Idea
import frflow.protocol.*
import frflow.protocol.ObligationName.{Cover, Eval, EvalImpl, Expect, Impl, RootImpl}
import frflow.protocol.ObligationStatus.*
import java.nio.file.Path
import scala.util.chaining.*

/** The knowledge base as data, without decisions: what agents read (`.frflow/kb.json`), and what the ledger's review reads. */
object Snapshots:
  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(n => NodeId(n.id)).toList

  def of(a: Analysis): Snapshot =
    val kb = a.kb
    val g = a.generate
    Snapshot(name = kb.name, nodes = kb.ordered.map(node(a, _)), idea = a.idea, ideaFile = kb.idea, warnings = Governance.warnings(a),
      root = kb.root.map(r => NodeId(r.id)), definitions = ids(kb.definitions), trusted = ids(g.trusted), exportedAt = a.inputs.now,
      opaques = kb.opaques.map(o => OpaqueTerm(o.name, o.means, g.inForce.get(o.name).map(d => NodeId(d.id)))),
      params = kb.params.map(p => ParamTerm(p.name, p.means, kb.isOp(p.name), g.inForce.get(p.name).map(d => NodeId(d.id)),
        kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).toMap.getOrElse(p.name, ""))),
      types = kb.types.map(t => TypeText(t.name, t.lean)),
      defs = kb.defs.map(d => DefText(d.name, d.lifted.source)))

  private def node(a: Analysis, n: Node[?]): SnapNode =
    val kb = a.kb
    val g = a.generate
    val id = NodeId(n.id)
    val check = a.current(n)
    def outcome(name: ObligationName) = check.flatMap(_.result(name)).fold(Outcome.unchecked)(Outcome.of)
    val c = a.content(n)
    // What Lean computes of each example written (not generated ones), against what Scala does.
    val examples = a.examples(n).zipWithIndex.map { (r, i) =>
      def lean(name: ObligationName) = Option.when(i < n.cases.size)(outcome(name))
      ExampleView(r.example.note, r.example.givens, r.example.call, r.example.expected, Option.when(r.contract != "ok")(r.contract),
        r.implementation.filter(_ != "ok"), lean(Eval(i)), if g.provenImpl(n).isEmpty then None else lean(EvalImpl(i)))
    }
    SnapNode(id = id, kind = n.kind, content = c, hash = c.hash, parents = ids(kb.parentsOf(n)), parts = ids(kb.children(n)),
      replaces = n.replaced.map(r => NodeId(r.id)), op = n.op.map(_.name), defines = n.defines,
      uses = ids(kb.definitionsUsed(n, g.inForce)), relies = ids(g.callees(n)), rule = n.isInvariant,
      // The root met by doing nothing: it says only what must not happen (see the ledger's `Proofs.unproven`).
      idle = Option.when(kb.isRoot(n))(a.idleOf(n)).flatten,
      status = Option.when(kb.isStatement(n))(check.orElse(a.checks.get(id).filter(_.hash == a.checkHash(n))).fold(CheckStatus.Unchecked)(_.status)),
      leaf = n.kind == NodeKind.Claim && kb.parts(n).isEmpty, examples = examples, code = a.code(n), split = a.split(n),
      invariants = n.kept.map(kept(a, n, _)),
      expectations = n.expected.zipWithIndex.map { case ((st, l), i) => outcome(Expect(i)).pipe(o => Expectation(st, l.source, o.status, o.detail)) },
      implementationProof = g.provenImpl(n).map(d => outcome(Impl).pipe(o => ImplProof(d.name, o.status, o.detail))),
      rootImpl = Option.when(kb.isRoot(n))(outcome(RootImpl)),
      covers = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty))),
      exempts = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty))),
      obligations = g.obligations(n).map(o => ObligationText(o.name.lean, o.statement, o.description)),
      proof = a.proofOf(n).map(src => ProofFile("lean/" + g.layout.proofs(n.id).path, src)),
      holds = if g.formal(n) then g.holdsStatement(n) else "", lean = if g.formal(n) then g.spec(n) else "",
      messages = check.orElse(a.checks.get(id).filter(_.status == CheckStatus.Waiting)).toList.flatMap(_.messages))

  /** An invariant a contract keeps: the view lists all the result holds of it, and the invariant's `complete`, this contract
    * among its parts. Lean showing it holds without the contract leaves it `open`; a try that found no proof proves nothing.
    */
  private def kept(a: Analysis, n: Node[?], k: Keep): Kept =
    val (st, detail) =
      if k.view.isEmpty then (Exempt, k.exempt)
      else
        val inv = a.split(k.invariant)
        val cover = a.current(n).flatMap(_.result(Cover(k.invariant.id))).map(r => (r.status, s"coverage: ${r.detail}"))
        val complete = inv.map(s => (s.complete.status, s.complete.detail))
        val needed = inv.flatMap(_.needed.find(_.id == NodeId(n.id))).map(p => (p.status, p.detail))
        val notNeeded = needed.filter(_._1 == Shown).map(c => (Open, c._2))
        (cover.toList ++ complete ++ notNeeded).find(_._1 != Proven).getOrElse(complete.fold((Unchecked, "not checked yet"))(_ => (Proven,
          s"${k.invariant.id} follows from the contracts that keep it, ${n.id} among them" +
            needed.filter(_._1 == NotShown).fold("")(x => s"; needed: not shown otherwise — ${x._2}"))))
    Kept(NodeId(k.invariant.id), k.view.fold("")(_.source), k.invariant.rule.fold("")(_.source), st, detail)

/** What `status` warns of besides decisions, proofs and signatures (the snapshot carries these; the ledger's are read live). */
object Governance:
  def warnings(a: Analysis): List[String] =
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
    // Formal contracts whose translation no example cross-checks: checked, and none of their examples evaluated in Lean.
    val uncrossed = kb.nodes.filter(c => c.kind == NodeKind.Contract && c.cases.nonEmpty).flatMap { c =>
      a.current(c).filter(k => !k.obligations.exists(o => o.name.isInstanceOf[Eval] && o.status == Proven)).map(_ =>
        s"${c.id}: none of its examples is evaluated in Lean, so nothing checks that the Lean means what the Scala does: give its parameters values Lean has (bindTable for a lookup)")
    }
    missing ++ owners ++ ideaCoverage ++ orphans ++ ungoverned(a).map(f => s"$f is governed by no node: govern it (a design node) or move it") ++
      uncrossed

  /** Source files no node governs, other than the model's own: code that can change unnoticed (see `Inputs.projectSources`). */
  def ungoverned(a: Analysis): List[String] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(a.ws.root)
    val governed = a.kb.nodes.flatMap(a.code).flatMap(_.files).map(f => abs(a.ws.root.resolve(f))).toSet ++
      a.kb.modelFiles.map(f => abs(Path.of(f)))
    // The file that puts the knowledge base together (its concerns listed) is the model's too.
    a.inputs.sources.toList.collect { case (p, text) if !governed(p) && !text.contains("KnowledgeBase(\"") => p }
      .map(p => if p.startsWith(root) then root.relativize(p).toString else p.toString).sorted
