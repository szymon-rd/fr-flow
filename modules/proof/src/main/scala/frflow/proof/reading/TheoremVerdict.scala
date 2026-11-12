package frflow.proof.reading

/** Whether Rocq accepted one lemma of a file: proven, not in a file Rocq read, or failed with what Rocq said. */
enum TheoremVerdict:
  case Proven, Missing
  case Failed(errors: List[Diagnostic])
