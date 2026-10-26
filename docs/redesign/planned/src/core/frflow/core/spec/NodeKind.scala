package frflow.core.spec

/** The kinds a developer reads and the snapshot writes (`kind`): a classification of statements, computed by
  * `Statement.kind`, never stored beside one.
  */
enum NodeKind:
  case Claim, Invariant, Contract, Assumption, Definition, Design
