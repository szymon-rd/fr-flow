package frflow.project.port

import frflow.core.name.{NodeId, RelPath}
import frflow.wire.file.Unreadable

/** What stops the shell, raised in `F` (no caller nearby goes on): Lean's build tool does not run; a node named that
  * the model does not have; a file FrFlow must read that does not read (the ledger); the developer's signing key
  * missing, or not a key; a `.lean` file under `lean/Proofs/` that is no node's proof file.
  */
enum FrFlowError extends scala.util.control.NoStackTrace:
  case NoLean
  case UnknownNode(id: NodeId)
  case NotRead(problem: Unreadable)
  case NoKey(file: String)
  case NotAKey(file: String, problem: String)
  /** `.lean` files under `lean/Proofs/` that are no node's proof file (`lean/Proofs/<Model>/<Node>.lean`): Lake builds
    * one a proof imports, unread by the proof rules, so nothing is checked while one is there.
    */
  case StrayProofs(files: List[RelPath])
