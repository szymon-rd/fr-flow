package frflow
package boundary

/** What a fact says of its store. */
enum FactKind:
  /** What the store holds when the system starts: `rule`, a forall over the state, read as its variable and body. */
  case Initially(rule: Tree)
  /** Only these programs (flows proven against the store's model) change it. */
  case WrittenOnlyBy(programs: List[Param[?]])
  /** One run changes it at a time: runs do not interleave. */
  case OneRunAtATime
