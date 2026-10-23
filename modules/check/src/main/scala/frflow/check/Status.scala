package frflow
package check

import frflow.ledger.Reports
import frflow.lean.ObligationName
import frflow.protocol.{NodeKind as _, *}

/** Where a knowledge base stands, as `status` reports it: the decisions (the annotated snapshot), what the
  * root rests on, how far the proofs reach, notes and warnings; and whether it is complete (the CI gate).
  */
final case class Status(annotated: Annotated, trusted: Option[Status.Trusted], reach: Status.Reach, notes: List[String],
    warnings: List[String]):
  /** Every node accepted, proven and passing its examples, and nothing to warn of. */
  def ok: Boolean = Reports.complete(annotated) && warnings.isEmpty

object Status:
  /** What the root rests on, of the code: the hypotheses of `root_impl`, with its status ("not checked" when
    * there is no current check), and each trusted node with its kind.
    */
  final case class Trusted(rootImpl: String, nodes: List[(NodeId, String)])

  /** How far the proofs reach: splits proven, splits out of Lean, and contracts proven down to their code (a
    * proven define, with any running code checked against it), checked by running only, or reviewed only.
    *
    * @param beside   the contracts proven down to their code whose running code is checked against the define
    * @param examples the examples Lean evaluated as Scala does (the translation's cross-check)
    */
  final case class Reach(splits: Int, provenSplits: Int, notProvenYet: List[NodeId], outOfLean: List[NodeId], contracts: Int,
      provenDown: List[NodeId], beside: List[String], byRunning: List[NodeId], designs: List[NodeId], examples: Option[Examples])

  /** Examples evaluated in Lean as in Scala, of how many; probes near them; contracts with none evaluated. */
  final case class Examples(evaluated: Int, total: Int, probes: Int, none: List[NodeId])

  def of(a: Analysis): Status =
    Status(a.annotated, trusted(a), reach(a), Governance.notes(a), Governance.warnings(a))

  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(n => NodeId(n.id)).toList

  def trusted(a: Analysis): Option[Trusted] =
    val g = a.generate
    a.kb.root.filter(g.formal).map { r =>
      Trusted(a.current(r).flatMap(_.result(ObligationName.RootImpl.lean)).fold("not checked")(_.status.toString),
        g.trusted.map(t => NodeId(t.id) -> Analysis.shownKind(t)))
    }

  def reach(a: Analysis): Reach =
    val kb = a.kb
    val g = a.generate
    val splits = kb.nodes.filter(n => kb.isStatement(n) && kb.parts(n).nonEmpty)
    val formalSplits = splits.filter(n => g.splitParts(n).isDefined)
    val proven = formalSplits.filter(n => a.split(n).exists(_.proven))
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    val down = provenDown(a)
    val beside = down.flatMap(c => kb.implementation(c).filter(_.wiring.nonEmpty).flatMap(i => i.proven.map(d =>
      s"${c.id}: proven define ${d.name}; running code ${Reports.runningCode(i.wiring)} checked against it")))
    Reach(splits.size, proven.size, ids(formalSplits.diff(proven)), ids(splits.diff(formalSplits)), contracts.size, ids(down), beside,
      ids(contracts.filter(c => kb.implementation(c).exists(_.proven.isEmpty))), ids(kb.nodes.filter(_.kind == NodeKind.Design)), examples(a))

  /** The contracts proven down to their code: their implementation is a proven define, proven to meet
    * them (running code beside it, if any, is checked against it).
    */
  def provenDown(a: Analysis): List[Node[?]] =
    a.kb.nodes.filter(c => c.kind == NodeKind.Contract && a.generate.provenImpl(c).isDefined &&
      a.current(c).exists(k => k.status == CheckStatus.Proven && k.result(ObligationName.Impl.lean).exists(_.status == ObligationStatus.Proven)))

  private def examples(a: Analysis): Option[Examples] =
    val per = a.kb.nodes.filter(c => c.post.isDefined && a.generate.formal(c) && c.cases.nonEmpty).map { c =>
      val rs = a.current(c).toList.flatMap(_.obligations)
      (c, rs.count(o => Analysis.isExample(o) && o.status == ObligationStatus.Proven), c.cases.size)
    }
    val probes = a.kb.nodes.flatMap(c => a.current(c).toList.flatMap(_.obligations)).count(o => ObligationName.parse(o.name).exists(_.isProbe) && o.status == ObligationStatus.Proven)
    Option.when(per.nonEmpty)(Examples(per.map(_._2).sum, per.map(_._3).sum, probes, ids(per.filter(_._2 == 0).map(_._1))))

  // ---------------------------------------------------------------------------
  // As text (what `status` prints today)
  // ---------------------------------------------------------------------------

  def text(s: Status): String =
    Reports.tree(s.annotated) + "\n\n" + s.trusted.fold("")(trustedText) + reachText(s.reach) + "\n" + Reports.load(s.annotated) +
      s.notes.map("note: " + _ + "\n").mkString + s.warnings.map("warning: " + _ + "\n").mkString +
      (if s.ok then "Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass."
       else "Not every node is accepted, proven, and passing its examples, or there are warnings.") + "\n"

  def trustedText(t: Trusted): String =
    s"Trusted (the hypotheses of root_impl, ${t.rootImpl}): ${if t.nodes.isEmpty then "nothing" else t.nodes.map((id, k) => s"$id ($k)").mkString(", ")}.\n"

  def reachText(r: Reach): String =
    s"Proofs: ${r.provenSplits} of ${r.splits} splits proven in Lean" +
      (if r.notProvenYet.nonEmpty then s" (${r.notProvenYet.mkString(", ")} not proven yet)" else "") +
      (if r.outOfLean.nonEmpty then s" (${r.outOfLean.mkString(", ")} out of Lean)" else "") + "; " +
      s"${r.provenDown.size} of ${r.contracts} contracts proven down to their code" +
      (if r.beside.nonEmpty then s" (${r.beside.mkString("; ")})" else "") +
      (if r.byRunning.nonEmpty then s", checked by running for ${r.byRunning.mkString(", ")}" else "") +
      (if r.designs.nonEmpty then s"; ${r.designs.size} design decision(s) govern code reviewed only (${r.designs.mkString(", ")})" else "") +
      r.examples.fold("") { e =>
        s"; examples evaluated in Lean as in Scala: ${e.evaluated} of ${e.total}, and ${e.probes} probe(s) near them" +
          (if e.none.nonEmpty then s" (none for ${e.none.mkString(", ")}: unchecked, or its parameters are functions)" else "")
      } + ".\n"
