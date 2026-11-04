package frflow.proof.reading

/** Whether Lean proved one theorem of a file: proven, not in the file, resting on `sorry`, or failed with Lean's
  * errors.
  */
enum TheoremVerdict:
  case Proven, Missing, UsesSorry
  case Failed(errors: List[Diagnostic])
