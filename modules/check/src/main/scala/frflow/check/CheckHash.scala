package frflow
package check

import frflow.lean.LeanSource
import frflow.protocol.{Hash, Sha}

/** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. It
  * covers the node's Lean, its proof file, the definitions it uses, its parts' and its callees' checks
  * (and, for the root, everything `root_impl` is composed of).
  */
object CheckHash:
  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 6

  /** What `root_impl` composes: every proof and every implementation. */
  def composed(a: Analysis, root: Node[?]): List[Node[?]] =
    val g = a.generate
    (g.trusted ++ a.kb.nodes.filter(c => g.provenImpl(c).isDefined) ++ a.kb.nodes.filter(g.formal))
      .distinctBy(_.id).filterNot(_ eq root)

  /** The hash of a node's check, given the hashes of what it composes (the root's; none for another node). */
  def of(a: Analysis, n: Node[?], composed: List[Hash]): Hash =
    val g = a.generate
    val kb = a.kb
    val isRoot = a.isRoot(n)
    val proof = a.proofOf(n)
    val lemmas = proof.filter(LeanSource.lemmaImports(_).nonEmpty).flatMap(_ => a.lemmas).getOrElse("")
    // The specs of other nodes a proof imports: a change to them re-checks it.
    val imported = proof.fold("")(src => s"(?m)^\\s*import\\s+FrFlowGen\\.${java.util.regex.Pattern.quote(kb.name)}\\.(\\w+)\\.Spec".r
      .findAllMatchIn(src).map(_.group(1)).filter(_ != n.id).flatMap(kb.node).filter(g.formal).map(g.spec).mkString)
    // A node's proofs read its parts' and callees' statements (and its `holds`, its parts' `holds`, over the
    // leaves below them), not how those are proven or coded: a change of code below re-checks only the
    // contract and the root's `root_impl`, not every ancestor.
    val below = (kb.parts(n) ++ g.callees(n)).filter(g.formal).distinctBy(_.id).filterNot(_ eq n).map(g.spec).mkString
    val partsHold = kb.parts(n).filter(g.formal).filterNot(_ eq n).map(g.holdsStatement).mkString
    Hash(Sha.parts((Seq(g.spec(n), g.auto(n), g.theorems(n), g.checks(n), g.evalFile(n).getOrElse(""),
      g.provenImpl(n).fold("")(_ => g.impl(n)), if isRoot then g.rootImpl.fold("")(_._2) else "",
      proof.getOrElse(""), lemmas, imported, below, partsHold,
      // `root_impl` composes every proof and every implementation: the root depends on all of them.
      composed.map(_.value).mkString,
      CheckerVersion.toString) ++ g.declarationsUsedBy(n))*))
