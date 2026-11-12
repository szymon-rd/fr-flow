package frflow.core.spec

import frflow.core.term.language.Stated

/** What a written part is to the back ends: a term in final form (a formula, or a lambda's body over its inputs). */
enum Form:
  case Term(term: Stated[?])
