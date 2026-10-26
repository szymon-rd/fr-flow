package frflow
package boundary

/** What a fact says of its store, or of a program's inputs. */
enum FactKind:
  /** What the store holds when the system starts: `rule`, a forall over the state, read as its variable and body. */
  case Initially(rule: Tree)
  /** The store starts in a state meeting what always holds of it: its `always` claims, and its type's. */
  case StartsMeetingItsRules
  /** Only these programs (flows proven against the store's model) change it. */
  case WrittenOnlyBy(programs: List[Param[?]])
  /** One run changes it at a time: runs do not interleave. */
  case OneRunAtATime
  /** The program is called from outside only with inputs meeting what always holds of their types. */
  case CalledWithInputsMeetingTheirRules(program: Param[?])
