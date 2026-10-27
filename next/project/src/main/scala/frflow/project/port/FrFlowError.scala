package frflow.project.port

import frflow.core.name.NodeId
import frflow.wire.file.Unreadable

/** What stops the shell, raised in `F` (no caller nearby goes on): Lean's build tool does not run; a node named that
  * the model does not have; a file FrFlow must read that does not read (the ledger); the developer's signing key
  * missing, or not a key.
  */
enum FrFlowError extends scala.util.control.NoStackTrace:
  case NoLean
  case UnknownNode(id: NodeId)
  case NotRead(problem: Unreadable)
  case NoKey(file: String)
  case NotAKey(file: String, problem: String)
