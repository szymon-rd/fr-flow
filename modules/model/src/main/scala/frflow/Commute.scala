package frflow

/** Branches a flow runs at once (`what`), and what the proof must show of them: that the two orders of their steps,
  * `first` and `second` (lines of a `do` block, giving a value of type `result`), give the same result and the same
  * world, for every value of the variables they use (`free`) that meets `hyps`.
  */
private[frflow] final case class Commute(what: String, free: List[(String, String)], hyps: List[String], first: List[String],
    second: List[String], result: String)
