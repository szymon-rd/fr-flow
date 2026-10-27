package frflow
package check
package analysis

import frflow.lean.*
import frflow.protocol.*

/** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. */
object CheckHash:
  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 10

  /** What `root_impl` composes: every proof and every implementation. */
  def composed(a: Analysis, root: Node[?]): List[Node[?]] =
    val g = a.generate
    (g.trusted ++ a.kb.nodes.filter(c => g.provenImpl(c).isDefined) ++ a.kb.nodes.filter(g.formal)).distinctBy(_.id).filterNot(_ eq root)

  /** The hash of a node's check, given the hashes of what it composes (the root's; none for another node). */
  def of(a: Analysis, n: Node[?], composed: List[Hash]): Hash =
    val g = a.generate
    val kb = a.kb
    val proof = a.proofOf(n)
    val lemmas = proof.filter(LeanSource.lemmaImports(_).nonEmpty).flatMap(_ => a.inputs.proofs.get("Lemmas")).getOrElse("")
    // The specs of other nodes a proof imports: a change to them re-checks it.
    val imported = proof.fold("")(src => s"(?m)^\\s*import\\s+FrFlowGen\\.${java.util.regex.Pattern.quote(kb.name)}\\.(\\w+)\\.Spec".r
      .findAllMatchIn(src).map(_.group(1)).filter(_ != n.id).flatMap(kb.node).filter(g.formal).map(g.spec).mkString)
    // A node's proofs read its parts' and callees' statements, with the terms they use (and its parts' `holds`, over
    // the leaves below them), not how those are proven or coded: a change of code below re-checks only the contract
    // and `root_impl`.
    val readBelow = (kb.parts(n) ++ g.callees(n)).filter(g.formal).distinctBy(_.id).filterNot(_ eq n)
    val below = (readBelow.map(g.spec) ++ readBelow.flatMap(g.declarationsUsedBy).distinct).mkString
    val partsHold = kb.parts(n).filter(g.formal).filterNot(_ eq n).map(g.holdsStatement).mkString
    Hash(Sha.parts((Seq(g.spec(n), g.auto(n), g.theorems(n), g.checks(n), g.evalFile(n).getOrElse(""),
      g.provenImpl(n).fold("")(_ => g.impl(n)), g.rootImpl(n).fold("")(_._2),
      proof.getOrElse(""), lemmas, imported, below, partsHold, composed.map(_.value).mkString,
      CheckerVersion.toString) ++ g.declarationsUsedBy(n))*))
