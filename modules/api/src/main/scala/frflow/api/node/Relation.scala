package frflow.api.node

/** How another node stands to a node in the DAG, read from the node's side: each relation today's `NodeDetails` held
  * as a list of its own (`parents`, `parts`, `designs`, `calls`, `calledBy`, `rivals`), the premises a node assumes
  * and is assumed by, and the rules it uses (2.4: each below it or an assumption of `always` it lists, no part of its
  * step), apart by whether it takes the rule (`Rule`) or not (`UnusedRule`).
  */
enum Relation:
  case Parent, Part, Rule, UnusedRule, Design, Assumes, AssumedBy, Calls, CalledBy, Rival
