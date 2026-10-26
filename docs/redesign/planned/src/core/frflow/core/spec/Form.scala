package frflow.core.spec

import frflow.core.expr.Prog
import frflow.core.term.Stated

/** What a written part is to the back ends: a term in final form (a formula, or a lambda's body over its inputs), or a
  * program's recorded steps over its inputs (their final form is the program over `Flow`; the recording gives these).
  */
enum Form:
  case Term(term: Stated[?])
  case Steps(steps: Prog[Stated[?]])
