package frflow
package boundary

/** What a fact says of its store, or of a program's inputs. */
enum FactKind:
  /** What the store holds when the system starts: `rule`, a forall over the state, read as its variable and body. */
  case Initially(rule: Tree)
  /** The store starts in a state satisfying an `always` claim about it, declared before the fact. */
  case StartsSatisfying(claim: Node[?])
  /** Only these programs (flows proven against the store's model) change it. */
  case WrittenOnlyBy(programs: List[Param[?]])
  /** One run changes it at a time: runs do not interleave. */
  case OneRunAtATime
  /** The program is called from outside only on inputs meeting `condition`, a forall over the input. */
  case CalledOnlyWith(program: Param[?], condition: Tree)
