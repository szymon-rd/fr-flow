package frflow.proof.verdict

/** One build of a module by the prover, with its report (`reading.RocqReport`). */
enum ProverRun:
  case Built(output: String)
  case Failed(output: String)
  case TimedOut(output: String)
