package frflow.project.pipeline

import frflow.core.name.{NodeId, RelPath}
import frflow.proof.reading.ProofFile

/** What Rocq reads beside the modules FrFlow generates: the developer's proof files, each
  * `rocq/Proofs/<Model>/<node>.v` (the shared lemmas' as `Lemmas`); any other `.v` file under `rocq/Proofs/`
  * (`strays`: a check would compile one a proof imports, unread by the rules, so no check runs while one is there);
  * and FrFlow's Rocq library, by its version.
  */
final case class ProofSources(files: Map[NodeId, ProofFile], strays: List[RelPath], library: String)
