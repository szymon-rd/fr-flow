package frflow.dsl.vocab

import frflow.core.term.Body
import frflow.dsl.term.{LeanType, Recorded, Term}

/** What a Definition given its meaning on the spot is besides its lambda: a define's body, which a call names; a
  * program's steps on its inputs' terms (of the types `inputs`, in order), which production runs (`eval.Running`).
  */
enum Spot:
  case Define(body: Body[?])
  case Steps(inputs: List[LeanType[?]], on: List[Term[?]] => Recorded[?])
