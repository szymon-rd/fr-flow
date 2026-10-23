package frflow.api

import frflow.ledger.Reports
import frflow.protocol.*

/** How far the proofs reach, from the snapshot: what `status` reports besides the tree. */
object Proofs:
  import ObligationStatus.{Informal, Proven}

  /** A contract proven down to its code: its implementation is a proven define, proven to meet it. */
  def provenDown(n: SnapNode): Boolean =
    n.kind == NodeKind.Contract && n.implementationProof.exists(_.status == Proven) && n.status.contains(CheckStatus.Proven)

  /** The running code checked against a proven define (the `runs:` line of its implementation). */
  def running(n: SnapNode): Option[String] =
    n.content.text("implementation").linesIterator.find(_.startsWith("runs: ")).map(r => Reports.runningCode(r.stripPrefix("runs: ")))

  /** `probes`: how many probes near the examples Lean evaluated (they are in the checks, not the snapshot). */
  def coverage(s: Snapshot, probes: Int): Coverage =
    val splits = s.nodes.filter(_.split.isDefined)
    val (outOfLean, formal) = splits.partition(_.split.exists(_.complete.status == Informal))
    val contracts = s.nodes.filter(_.kind == NodeKind.Contract)
    val down = contracts.filter(provenDown)
    // The examples written for a formal node, which Lean evaluates as Scala does.
    val inLean = s.nodes.filter(_.examples.exists(_.lean.isDefined))
    def evaluated(n: SnapNode) = n.examples.count(_.lean.exists(_.status == Proven))
    Coverage(
      splits = splits.size,
      splitsProven = formal.count(_.split.exists(_.proven)),
      notProvenYet = formal.filterNot(_.split.exists(_.proven)).map(_.id),
      outOfLean = outOfLean.map(_.id),
      contracts = contracts.size,
      provenDown = down.map(_.id),
      runningBeside = down.flatMap(c => c.implementationProof.zip(running(c)).map((p, r) => RunningCode(c.id, p.name, r))),
      checkedByRunning = contracts.filter(c => c.implementationProof.isEmpty && c.content.text("implementation").nonEmpty).map(_.id),
      designs = s.nodes.filter(_.kind == NodeKind.Design).map(_.id),
      examplesEvaluated = inLean.map(evaluated).sum,
      examplesInLean = inLean.map(_.examples.count(_.lean.isDefined)).sum,
      probes = probes,
      noneEvaluated = inLean.filter(evaluated(_) == 0).map(_.id))
