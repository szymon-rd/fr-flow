package frflow.project.pipeline

import frflow.core.name.{NodeId, RelPath}
import frflow.proof.reading.ProofFile

/** What Lean reads beside the modules FrFlow generates: the developer's proof files, each
  * `lean/Proofs/<Model>/<Node>.lean` (the shared lemmas' as `Lemmas`); any other `.lean` file under `lean/Proofs/`
  * (`strays`: Lake would build one a proof imports, unread by the rules, so no check runs while one is there); and
  * FrFlow's Lean library, by its version.
  */
final case class LeanSources(proofs: Map[NodeId, ProofFile], strays: List[RelPath], library: String)

object LeanSources:
  /** The Lean FrFlow's library is built with (`next/proof/lean/lean-toolchain`), which the project's Lean uses too. */
  val Toolchain: String = "leanprover/lean4:v4.35.0\n"
