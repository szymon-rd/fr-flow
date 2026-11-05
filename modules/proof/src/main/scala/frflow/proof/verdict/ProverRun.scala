package frflow.proof.verdict

/** One run of Lean on a module, with Lean's output (its messages are read by `reading.LeanOutput`). */
enum ProverRun:
  case Built(output: String)
  case Failed(output: String)
  case TimedOut(output: String)
