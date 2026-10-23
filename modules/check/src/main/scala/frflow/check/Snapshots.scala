package frflow
package check

import frflow.protocol.*
import frflow.protocol.ObligationName.{Cover, Eval, EvalImpl, Expect, Impl, RootImpl, Tried}
import frflow.protocol.ObligationStatus.*

/** The knowledge base as data, from the Scala definitions and the checks, without decisions: what agents
  * read (`.frflow/kb.json`), and what the ledger's review reads.
  */
object Snapshots:
  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(n => NodeId(n.id)).toList

  def of(a: Analysis): Snapshot =
    val kb = a.kb
    val g = a.generate
    Snapshot(
      name = kb.name,
      nodes = kb.ordered.map(node(a, _)),
      idea = a.idea,
      ideaFile = kb.idea,
      warnings = Governance.warnings(a),
      root = kb.root.map(r => NodeId(r.id)),
      definitions = ids(kb.definitions),
      trusted = ids(g.trusted),
      exportedAt = a.inputs.now,
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
    SnapNode(
      id = id,
      kind = n.kind,
      content = c,
      hash = c.hash,
      parents = ids(kb.parentsOf(n)),
      parts = ids(kb.children(n)),
      replaces = n.replaced.map(r => NodeId(r.id)),
      op = n.op.map(_.name),
      defines = n.defines,
      uses = ids(kb.definitionsUsed(n, g.inForce)),
      relies = ids(g.callees(n)),
      rule = n.isInvariant,
      // The root met by doing nothing: it says only what must not happen (see the ledger's `Proofs.unproven`).
      idle = Option.when(kb.isRoot(n))(a.idleOf(n)).flatten,
      status = Option.when(kb.isStatement(n))(check.orElse(a.checks.get(id).filter(_.hash == a.checkHash(n))).fold(CheckStatus.Unchecked)(_.status)),
      leaf = n.kind == NodeKind.Claim && kb.parts(n).isEmpty,
      examples = examples(a, n, outcome),
      code = a.code(n),
      split = a.split(n),
      invariants = n.kept.map(kept(a, n, _)),
      expectations = n.expected.zipWithIndex.map { case ((st, l), i) =>
        val o = outcome(Expect(i))
        Expectation(st, l.source, o.status, o.detail)
      },
      implementationProof = g.provenImpl(n).map { d =>
        val o = outcome(Impl)
        ImplProof(d.name, o.status, o.detail)
      },
      rootImpl = Option.when(kb.isRoot(n))(outcome(RootImpl)),
      covers = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty))),
      exempts = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty))),
      obligations = g.obligations(n).map(o => ObligationText(o.name.lean, o.statement, o.description)),
      proof = a.proofOf(n).map(src => ProofFile("lean/" + g.layout.proofs(n.id).path, src)),
      holds = if g.formal(n) then g.holdsStatement(n) else "",
      lean = if g.formal(n) then g.spec(n) else "",
      messages = check.orElse(a.checks.get(id).filter(_.status == CheckStatus.Waiting)).toList.flatMap(_.messages))

  /** What Lean computes of each example, against what Scala does (the examples written, not generated ones). */
  private def examples(a: Analysis, n: Node[?], outcome: ObligationName => Outcome): List[ExampleView] =
    a.examples(n).zipWithIndex.map { (r, i) =>
      def lean(name: ObligationName) = Option.when(i < n.cases.size)(outcome(name))
      ExampleView(r.example.note, r.example.givens, r.example.call, r.example.expected, Option.when(r.contract != "ok")(r.contract),
        r.implementation.filter(_ != "ok"), lean(Eval(i)), if a.generate.provenImpl(n).isEmpty then None else lean(EvalImpl(i)))
    }

  /** An invariant a contract keeps: what is proven, that the view lists all the result holds of it, and the
    * invariant's `complete`, this contract among its parts. Lean showing the invariant holds without it
    * leaves it `open`; a try that found no proof proves nothing, and is said apart.
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
