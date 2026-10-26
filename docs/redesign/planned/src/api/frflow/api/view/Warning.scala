package frflow.api.view

import frflow.core.name.{NodeId, RelPath}

/** What `status` warns of (docs/USAGE.md, Warnings): data, rendered by the CLI and the web view. */
enum Warning:
  case NoKey
  /** `.frflow/deciders` in the working tree differs from the committed list, which is the one that counts. */
  case DecidersUncommitted
  /** A decision signed by a key the committed list does not hold under its decider's name: it does not count. */
  case NotADecider(node: NodeId, by: String)
  case Unsigned(node: NodeId)
  case GovernedTwice(file: RelPath, by: List[NodeId])
  case Ungoverned(file: RelPath)
  case GovernedMissing(file: RelPath, by: NodeId)
  case ProofFileOfNoNode(file: RelPath)
  /** A consistency group Lean has not checked witnesses for: "consistency not proven" (or evidence only), its own
    * status, not a failing proof.
    */
  case ConsistencyNotProven(statements: List[NodeId])
  /** A claim nothing checks: no parts prove it, no proven code or value is checked against it, and the plain Scala it
    * is about cannot be tested against it (it has no Scala value): "not checked".
    */
  case NotChecked(node: NodeId)
  case Restates(node: NodeId, part: NodeId)
