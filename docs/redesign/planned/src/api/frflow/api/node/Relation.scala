package frflow.api.node

/** How another node stands to a node in the DAG, read from the node's side: each relation today's `NodeDetails` held
  * as a list of its own (`parents`, `parts`, `designs`, `definitions`, `usedBy`, `calls`, `calledBy`, `keptBy`,
  * `rivals`).
  */
enum Relation:
  case Parent, Part, Design, Uses, UsedBy, Calls, CalledBy, Keeps, KeptBy, Rival
