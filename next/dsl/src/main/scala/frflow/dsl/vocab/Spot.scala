package frflow.dsl.vocab

import frflow.core.term.Body
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.run.Recorded

/** What a Definition given its meaning on the spot is besides its lambda: a define's body, which a call names, and
  * whether it reads state (`worldly`: then it takes the world as its last input, owner §43); a program's steps on its
  * inputs' terms (of the types `inputs`, in order), which production runs (`eval.Running`).
  */
enum Spot:
  case Define(body: Body[?], worldly: Boolean)
  case Steps(inputs: List[LeanType[?]], on: List[Term[?]] => Recorded[?])
