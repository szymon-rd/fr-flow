package frflow.proof.obligation

/** How an obligation is to be met: by FrFlow's automation, by the developer's proof file, tried within a budget of
  * heartbeats (one-sided), or by evaluating (`frflow_eval`).
  */
enum Discharge:
  case Auto, Authored, Evaluate
  case Attempt(heartbeats: Int)
