package frflow.api.node

/** How another node stands to a node in the DAG, read from the node's side: each relation today's `NodeDetails` held
  * as a list of its own (`parents`, `parts`, `designs`, `calls`, `calledBy`, `rivals`), and the premises a node
  * assumes and is assumed by.
  */
enum Relation:
  case Parent, Part, Design, Assumes, AssumedBy, Calls, CalledBy, Rival
