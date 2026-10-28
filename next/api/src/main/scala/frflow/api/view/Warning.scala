package frflow.api.view

import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Decision, Uncounted}

/** What `status` warns of (docs/USAGE.md, Warnings): data, rendered by the CLI and the web view. */
enum Warning:
  /** The developer's signing key is missing or is not a key: nothing can be decided here. */
  case NoKey
  /** `.frflow/deciders` in the working tree differs from the committed list, which is the one that counts. */
  case DecidersUncommitted
  /** The ledger's base in the working tree is not the committed one, or the commit that made the committed one does
    * not hold the ledger text it names: it does not take (commit `.frflow/ledger-base` together with the ledger).
    */
  case BaseNotCommitted
  /** A decision in the ledger that does not count, and why: no deciders' list committed, its key not listed under its
    * decider's name (or no seal), its signature not verifying, or the node's committed history rewritten.
    */
  case NotCounted(node: NodeId, decision: Decision, why: Uncounted)
  /** A file under two designs: each would review it as its own. */
  case GovernedTwice(file: RelPath, by: List[NodeId])
  /** A source file no node governs, other than the model's own: code that can change unnoticed. */
  case Ungoverned(file: RelPath)
  /** A design governs a path that names no file of the project. */
  case GovernedMissing(file: RelPath, by: NodeId)
  /** A proof file of no node (after a rename or a removal): it proves nothing any more. */
  case ProofFileOfNoNode(file: RelPath)
  /** A consistency group Lean has not proven (evidence only is not proof): a failure, the whole model's proof red
    * and `complete` false (owner §28); said beside the overview so the developer knows what to add.
    */
  case ConsistencyNotProven(statements: List[NodeId])
  /** An `always(stored)` the states its store starts in are not proven to meet (`start_<node>`): what is said to hold
    * of every state reached is not shown to hold of the first.
    */
  case StartNotProven(statement: NodeId)
  /** A claim nothing checks: no parts prove it, no proven code or value is checked against it, and the plain Scala it
    * is about cannot be tested against it (it has no Scala value): "not checked".
    */
  case NotChecked(node: NodeId)
  /** Lean proves a node equivalent to its part (or a part to a conjunct of its parent): it says nothing of its own. */
  case Restates(node: NodeId, part: NodeId)
