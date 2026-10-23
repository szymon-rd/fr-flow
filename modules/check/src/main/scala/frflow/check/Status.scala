package frflow
package check

import frflow.ledger.Proofs
import frflow.lean.ObligationName
import frflow.protocol.{NodeKind as _, *}
import io.circe.Codec

/** Where a knowledge base stands, as `status` reports it: the decisions (the annotated snapshot), how far
  * the proofs reach, notes and warnings; and whether it is complete (the CI gate).
  */
final case class Status(annotated: Annotated, reach: Status.Reach, notes: List[String], warnings: List[String])
    derives Codec.AsObject:
  /** Every node accepted, proven and passing its examples, and nothing to warn of. */
  def ok: Boolean = Proofs.complete(annotated) && warnings.isEmpty

object Status:
  /** Running code checked against the proven define of a contract. */
  final case class RunningCode(node: NodeId, define: String, running: String) derives Codec.AsObject

  /** How far the proofs reach: splits proven, splits out of Lean, and contracts proven down to their code (a
    * proven define, with any running code checked against it), checked by running only, or reviewed only.
    *
    * @param beside   the contracts proven down to their code whose running code is checked against the define
    * @param examples the examples Lean evaluated as Scala does (the translation's cross-check)
    */
  final case class Reach(splits: Int, provenSplits: Int, notProvenYet: List[NodeId], outOfLean: List[NodeId], contracts: Int,
      provenDown: List[NodeId], beside: List[RunningCode], byRunning: List[NodeId], designs: List[NodeId], examples: Option[Examples])
      derives Codec.AsObject

  /** Examples evaluated in Lean as in Scala, of how many; probes near them; contracts with none evaluated. */
  final case class Examples(evaluated: Int, total: Int, probes: Int, none: List[NodeId]) derives Codec.AsObject

  def of(a: Analysis): Status =
    Status(a.annotated, reach(a), Governance.notes(a), Governance.warnings(a))

  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(n => NodeId(n.id)).toList

  def reach(a: Analysis): Reach =
    val kb = a.kb
    val g = a.generate
    val splits = kb.nodes.filter(n => kb.isStatement(n) && kb.parts(n).nonEmpty)
    val formalSplits = splits.filter(n => g.splitParts(n).isDefined)
    val proven = formalSplits.filter(n => a.split(n).exists(_.proven))
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    val down = provenDown(a)
    val beside = down.flatMap(c => kb.implementation(c).filter(_.wiring.nonEmpty).flatMap(i => i.proven.map(d =>
      RunningCode(NodeId(c.id), d.name, Proofs.runningCode(i.wiring)))))
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
