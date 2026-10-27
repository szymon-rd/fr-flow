package frflow.proof.verdict

import java.time.Instant

/** The theory's own check as recorded (`whole` in `.frflow/checks.json`): each consistency, vacuity and example
  * obligation's outcome, current while its key is the key of `Whole.lean` and of what it imports now.
  */
final case class WholeCheck(key: CheckKey, results: List[Result], at: Instant)
