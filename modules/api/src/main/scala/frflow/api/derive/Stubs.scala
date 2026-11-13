package frflow.api.derive

import frflow.api.view.Scaffolded
import frflow.core.name.{NodeId, RelPath}
import frflow.project.pipeline.Analysis
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.prover.lower.LowerObligation
import frflow.proof.obligation.ObligationName
import frflow.proof.reading.ProofRules
import frflow.proof.rocq.{RocqNames, RocqProject}
import frflow.proof.verdict.ObligationStatus

/** A node's proof file with a stub for each obligation its current check left open or failed (`complete` before any
  * check), less those the file already proves: the file created, or the stubs added at its end; or nothing to add.
  * A stub is given up (`Admitted`), which a proof file may not hold: it is the developer's to prove.
  */
private[api] object Stubs:
  def of(a: Analysis, id: NodeId): Either[Scaffolded, (RelPath, String)] =
    val file = RocqProject.path(Layout(a.decided.theory.name).proofs(id))
    val existing = a.inputs.proofs.files.get(id)
    val add = wanted(a, id).filterNot(existing.toList.flatMap(ProofRules.theorems).contains)
    if add.isEmpty then Left(Scaffolded.NothingToAdd)
    else Right(file -> existing.fold(fresh(a, id, add))(f => f.source.stripTrailing + "\n\n" + stubs(a, id, add)))

  private def wanted(a: Analysis, id: NodeId): List[ObligationName] =
    val required = a.obligations.find(_.node == id).toList.flatMap(_.required).map(_.name)
    a.current(id).fold(required.filter(_ == ObligationName.Complete))(c => c.results.collect {
      case r if (r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed) &&
        required.contains(r.name) => r.name
    })

  /** `Lemma <node>_Proofs_<obligation> : <node>_Obl_<obligation>.`, its proof to write. */
  private def stubs(a: Analysis, id: NodeId, names: List[ObligationName]): String =
    val of = (part: String, n: String) => RocqNames.joined(List(a.decided.theory.name.value, id.value, part, n))
    names.map(LowerObligation.name(_).text)
      .map(n => s"Lemma ${of("Proofs", n)} : ${of("Obl", n)}.\nProof.\nAdmitted.\n").mkString("\n")

  private def fresh(a: Analysis, id: NodeId, add: List[ObligationName]): String =
    s"""Require Export ${RocqProject.logical(Layout(a.decided.theory.name).ofNode(id, NodePart.Spec))}.
       |
       |(** Authored proofs of the obligations of ${id.value}. Each states exactly its obligation. *)
       |
       |""".stripMargin + stubs(a, id, add)
