package frflow
package check
package analysis

import frflow.protocol.*
import frflow.protocol.ObligationName.{Cover, Eval, EvalImpl, Expect, Impl, Initially, KeptBy, RootImpl}
import frflow.protocol.ObligationStatus.*
import scala.util.chaining.*

/** The knowledge base as data, without decisions (`.frflow/kb.json`): what tools read, and what the ledger's review reads. */
object Snapshots:
  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(n => NodeId(n.id)).toList

  def of(a: Analysis): Snapshot =
    val kb = a.kb
    val g = a.generate
    Snapshot(name = kb.name, nodes = kb.ordered.map(node(a, _)), idea = a.idea, ideaFile = kb.idea, warnings = Governance.warnings(a),
      root = kb.root.map(r => NodeId(r.id)), roots = ids(kb.roots), definitions = ids(kb.definitions),
      trusted = ids(g.trusted), exportedAt = a.inputs.now,
      opaques = kb.opaques.map(o => OpaqueTerm(o.name, o.means, g.inForce.get(o.name).map(d => NodeId(d.id)))),
      params = kb.params.map(p => ParamTerm(p.name, p.means, kb.isOp(p.name), g.inForce.get(p.name).map(d => NodeId(d.id)),
        kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).toMap.getOrElse(p.name, ""))),
      types = kb.types.map(t => TypeText(t.name, t.lean)),
      defs = kb.defs.map(d => DefText(d.name, d.lifted.source)),
      tested = ids(Snapshots.tested(a)), consistency = proving.Consistent.current(a))

  /** What root_impl assumes that is code tested against its contract (not an assumption about the outside). */
  def tested(a: Analysis): List[Node[?]] = a.generate.trusted.filter(c => Testing.testable(a.kb, c).exists(_.proven.isEmpty))

  private def node(a: Analysis, n: Node[?]): SnapNode =
    val kb = a.kb
    val g = a.generate
    val id = NodeId(n.id)
    val check = a.current(n)
    def outcome(name: ObligationName) = check.flatMap(_.result(name)).fold(Outcome.unchecked)(Outcome.of)
    val c = a.content(n)
    // What Lean computes of each example written (not generated ones), against what Scala does.
    val examples = a.examples(n).zipWithIndex.map { (r, i) =>
      def lean(name: ObligationName) = Option.when(i < kb.casesOf(n).size)(outcome(name))
      ExampleView(r.example.note, r.example.givens, r.example.call, r.example.expected, r.failing,
        r.implementation.filter(_ != "ok"), lean(Eval(i)), if g.provenImpl(n).isEmpty then None else lean(EvalImpl(i)),
        r.example.written)
    }
    SnapNode(id = id, kind = n.kind, content = c, hash = c.hash, parents = ids(kb.parentsOf(n)), parts = ids(kb.children(n)),
      replaces = n.replaced.map(r => NodeId(r.id)), op = n.op.map(_.name), defines = n.defines,
      uses = ids(kb.definitionsUsed(n, g.inForce)), relies = ids(g.reliedOn(n)),
      rule = n.isInvariant,
      // The root met by doing nothing: it says only what must not happen (see the ledger's `Proofs.unproven`).
      idle = Option.when(kb.isRoot(n))(a.idleOf(n)).flatten,
      status = Option.when(kb.isStatement(n))(check.orElse(a.checks.get(id).filter(_.hash == a.checkHash(n))).fold(CheckStatus.Unchecked)(_.status)),
      // A claim nothing below proves: no parts, no code, not an `always` (proven kept by the code that writes it).
      leaf = n.kind == NodeKind.Claim && kb.parts(n).isEmpty && !n.isAlways && kb.implementation(n).isEmpty,
      examples = examples, code = a.code(n), split = a.split(n),
      invariants = n.kept.map(kept(a, n, _)),
      expectations = n.expected.zipWithIndex.map { case ((st, l), i) => outcome(Expect(i)).pipe(o => Expectation(st, l.source, o.status, o.detail)) },
      implementationProof = g.provenImpl(n).map(d => outcome(Impl).pipe(o => ImplProof(d.name, o.status, o.detail))),
      rootImpl = Option.when(kb.isRoot(n) && !n.isAlways)(outcome(RootImpl)),
      covers = if !n.isInvariant then Nil
        else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty))),
      exempts = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty))),
      obligations = g.obligations(n).map(o => ObligationText(o.name.lean, o.statement, o.description)),
      proof = a.proofOf(n).map(src => ProofFile("lean/" + g.layout.proofs(n.id).path, src)),
      holds = if g.formal(n) then g.holdsStatement(n) else "", lean = if g.formal(n) then g.spec(n) else "",
      messages = check.orElse(a.checks.get(id).filter(_.status == CheckStatus.Waiting)).toList.flatMap(_.messages),
      tested = a.tested(n), runtime = kb.runTime(n), premises = ids(kb.premisesOf(n)),
      alwaysProofs = alwaysProofs(a, n, outcome))

  /** What an `always` claim rests on, as proven: each program writing what holds it keeps it; a store's start meets
    * it; and the steps whose code hands a value of its type to a claim assuming it (a part assumes it, the step
    * does not) show it of that value (`complete` of the step).
    */
  private def alwaysProofs(a: Analysis, n: Node[?], outcome: ObligationName => Outcome): List[AlwaysProof] =
    val kb = a.kb
    val kept = kb.writers(n).flatMap(_.op).map(_.name).map(p => AlwaysProof(KeptBy(p).lean, p, outcome(KeptBy(p))))
    val start = kb.premisesOf(n).find(_.initially.isDefined).filter(_ => n.always.exists(_.store.isDefined))
      .map(s => AlwaysProof(Initially.lean, s.id, outcome(Initially)))
    def assumes(c: Node[?]) = kb.invariantsUsedBy(c).exists(_ eq n)
    val handed = kb.nodes.filter(p => kb.isStatement(p) && !assumes(p) && kb.parts(p).exists(assumes)).map { p =>
      val o = a.current(p).flatMap(_.result(ObligationName.Complete)).fold(Outcome.unchecked)(Outcome.of)
      AlwaysProof(ObligationName.Complete.lean, p.id, o)
    }
    if n.isAlways then kept ++ start ++ handed else Nil

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
