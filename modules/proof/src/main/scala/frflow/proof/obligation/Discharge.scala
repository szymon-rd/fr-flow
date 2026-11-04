package frflow.proof.obligation

/** How an obligation is to be met: by FrFlow's automation, by the developer's proof file, tried within a budget of
  * heartbeats (one-sided), by the witnesses FrFlow derived (`⟨w₁, …, by frflow_witness⟩`), or by nothing yet: a
  * statement no witness was found for, which shows "not proven" until the developer proves it.
  */
enum Discharge:
  case Auto, Authored
  case Attempt(heartbeats: Int)
  case Witnessed(by: List[Supplied])
  case Unwitnessed
