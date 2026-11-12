package frflow.dsl.vocab

import frflow.core.term.language.Body

/** What a Definition given its meaning on the spot is besides its lambda: a define's body, which a call names. */
enum Spot:
  case Define(body: Body[?])
