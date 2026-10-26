package frflow.core.code

/** How a contract's code is checked where it runs (`service`), when the developer chose it: every call, one call in
  * `oneIn` (with a seed: drawn at random), or none. Unchosen, the default follows from the code (`runtime.Policy`).
  */
enum RunCheck:
  case EveryCall
  case Sampled(oneIn: Int, seed: Option[Long])
  case Never
