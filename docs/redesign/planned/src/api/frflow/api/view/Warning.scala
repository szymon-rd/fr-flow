package frflow.api.view

import frflow.core.name.{NodeId, RelPath}

/** What `status` warns of (docs/USAGE.md, Warnings): data, rendered by the CLI and the web view. */
enum Warning:
  case NoKey
  /** Decisions bound in the old form (`Format.V1`), until `confirm --rebind`. */
  case OldForm(decisions: Int)
  case Unsigned(node: NodeId)
  case GovernedTwice(file: RelPath, by: List[NodeId])
  case Ungoverned(file: RelPath)
  case GovernedMissing(file: RelPath, by: NodeId)
  case ProofFileOfNoNode(file: RelPath)
  case NoExampleInLean(contract: NodeId)
  case Restates(node: NodeId, part: NodeId)
