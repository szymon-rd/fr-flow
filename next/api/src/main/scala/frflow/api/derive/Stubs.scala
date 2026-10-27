package frflow.api.derive

import frflow.api.view.Scaffolded
import frflow.core.name.{NodeId, RelPath}
import frflow.project.pipeline.Analysis
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.ObligationName
import frflow.proof.reading.{ProofFile, ProofRules}
import frflow.proof.verdict.ObligationStatus

/** A node's proof file with a stub for each obligation its current check left open or failed (`complete` before any
  * check), less those the file already proves: the file created, or the stubs added before its end; or why not
  * (nothing to add, or the file's end is not found).
  */
private[api] object Stubs:
  def of(a: Analysis, id: NodeId): Either[Scaffolded, (RelPath, String)] =
    val file = Layout(a.decided.theory.name).proofs(id).file
    val existing = a.inputs.proofs.get(id)
    val add = wanted(a, id).filterNot(existing.toList.flatMap(ProofRules.theorems).contains)
    if add.isEmpty then Left(Scaffolded.NothingToAdd)
    else existing.fold(Some(fresh(a, id, add)))(f => inserted(a, id, f, add))
      .toRight(Scaffolded.EndNotFound(file)).map(file -> _)

  private def wanted(a: Analysis, id: NodeId): List[ObligationName] =
    val required = a.obligations.find(_.node == id).toList.flatMap(_.required).map(_.name)
    a.current(id).fold(required.filter(_ == ObligationName.Complete))(c => c.results.collect {
      case r if (r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed) &&
        required.contains(r.name) => r.name
    })

  private def namespace(a: Analysis, id: NodeId): String = 
    Names.path(a.decided.theory.name.value, id.value).map(_.text).mkString(".")

  private def stubs(names: List[ObligationName]): String = names.map(LowerObligation.name(_).text)
    .map(n => s"theorem $n : Obl.$n := by\n  sorry\n\n").mkString

  private def fresh(a: Analysis, id: NodeId, add: List[ObligationName]): String =
    val ns = namespace(a, id)
    s"""import ${Layout(a.decided.theory.name).ofNode(id, NodePart.Spec).dotted}
       |
       |/-! Authored proofs of the obligations of ${id.value}. Each states exactly its `Obl`. -/
       |
       |namespace $ns.Proofs
       |open $ns
       |
       |""".stripMargin + stubs(add) + s"end $ns.Proofs\n"

  private def inserted(a: Analysis, id: NodeId, f: ProofFile, add: List[ObligationName]): Option[String] =
    val i = f.source.lastIndexOf(s"end ${namespace(a, id)}.Proofs")
    Option.when(i >= 0)(f.source.substring(0, i) + stubs(add) + f.source.substring(i))
