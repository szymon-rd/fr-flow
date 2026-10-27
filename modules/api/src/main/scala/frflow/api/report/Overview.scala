package frflow.api
package report

import frflow.ledger.{Proofs, Waiting}
import frflow.protocol.*
import io.circe.Codec

/** The counts every view closes with; `complete` is `View.ok`; `models`, the boundaries' models, trusted as `trusted`'s
  * nodes are, though no theorem takes them as hypotheses.
  */
final case class Overview(name: String, nodes: Int, proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int,
    proven: Int, trusted: List[NodeId], forDeveloper: Int, mechanical: Int, unsigned: Int, splits: Int, splitsProven: Int,
    contracts: Int, contractsProvenDown: Int, examplesInLean: Int, examplesAgreeing: Int, rootImpl: Option[ObligationStatus],
    warnings: Int, complete: Boolean, idea: Option[ReviewState] = None, contractsTested: Int = 0, testsPassing: Int = 0,
    tested: List[NodeId] = Nil, modelsRun: Int = 0, modelsPassing: Int = 0, runEveryCall: Int = 0, runSampled: Int = 0,
    runNotChecked: Int = 0, models: List[NodeId] = Nil, consistency: Option[Consistency] = None,
    facts: List[NodeId] = Nil, assumed: List[NodeId] = Nil)
    derives Codec.AsObject:
  def unproven: Int = nodes - proven

object Overview:
  def of(v: View): Overview = of(v, Waiting.forDeveloper(v.annotated))

  /** `waiting`: the nodes waiting for the developer (`Waiting.forDeveloper`). */
  private[api] def of(v: View, waiting: List[Reviewed]): Overview =
    val a = v.annotated
    val ns = a.nodes.map(_.node)
    def count(s: ReviewState) = a.nodes.count(_.state == s)
    val contracts = ns.filter(_.kind == NodeKind.Contract)
    def provenDown(c: SnapNode) = c.status.contains(CheckStatus.Proven) && c.implementationProof.exists(_.status == ObligationStatus.Proven)
    val inLean = ns.flatMap(_.examples.flatMap(_.lean))
    // How the running code is checked where it runs: what production does on each call.
    val runs = ns.flatMap(_.runtime).map(_.check)
    Overview(name = v.snapshot.name, nodes = a.nodes.size, proposed = count(ReviewState.Proposed), review = count(ReviewState.Review),
      accepted = count(ReviewState.Accepted), rejected = count(ReviewState.Rejected), gone = a.gone.size,
      proven = ns.count(Proofs.unproven(_).isEmpty), trusted = v.snapshot.trusted,
      forDeveloper = waiting.size + a.gone.size + v.ideaWaits.size, mechanical = waiting.count(_.review.mechanical),
      unsigned = v.unsigned.size,
      splits = ns.count(_.split.isDefined), splitsProven = ns.count(_.split.exists(_.proven)),
      contracts = contracts.size, contractsProvenDown = contracts.count(provenDown),
      examplesInLean = inLean.size, examplesAgreeing = inLean.count(_.status == ObligationStatus.Proven),
      rootImpl = v.snapshot.roots.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status)
        .reduceOption((a, b) => if a == ObligationStatus.Proven then b else a),
      warnings = v.warnings.size, complete = v.ok,
      idea = a.idea.map(_.state), contractsTested = ns.count(n => CodeProof.tested(n) && !model(n)),
      testsPassing = ns.count(n => CodeProof.tested(n) && !model(n) && n.tested.exists(_.passed)), tested = v.snapshot.tested,
      modelsRun = ns.count(model), modelsPassing = ns.count(n => model(n) && n.tested.exists(_.passed)),
      runEveryCall = runs.count(_ == RunCheck.EveryCall), runSampled = runs.count(_.isInstanceOf[RunCheck.Sampled]),
      runNotChecked = runs.count(_ == RunCheck.Never), models = a.nodes.filter(r => model(r.node)).map(_.id),
      consistency = v.snapshot.consistency,
      // The facts of how the system is run, decided: Lean has nothing to say of them.
      facts = a.nodes.filter(r => r.node.kind == NodeKind.Assumption && r.node.status.isEmpty && !model(r.node))
        .map(_.id),
      // What the other assumptions say, trusted though root_impl does not take them (what comes from outside).
      assumed = a.nodes.filter(r => r.node.kind == NodeKind.Assumption && r.node.status.nonEmpty && !model(r.node) &&
        !v.snapshot.trusted.contains(r.id)).map(_.id))

  private def model(n: SnapNode): Boolean = CodeProof.of(n).exists { case _: CodeProof.Model => true; case _ => false }
