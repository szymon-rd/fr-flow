package frflow.core.spec

/** The three kinds of nodes (owner §15), as a developer reads them and the snapshot writes them (`kind`): the
  * `Statement` case without its data.
  */
enum NodeKind:
  case Claim, Assumption, Design
