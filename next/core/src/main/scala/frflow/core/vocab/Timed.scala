package frflow.core.vocab

import frflow.core.name.SymbolName

/** What makes a model the clock (owner §47, as Cats Effect models time): its state is the time now, which only moves
  * on; steps of code take no time of their own. Its `now` reads the time, its `sleep` lets at least the
  * seconds given pass, and `elapse` is the world's own step, taken between runs, never called by code
  * (`TestControl.advance`). In Lean the world may also move the time on at each of the clock's steps (a tick of its
  * own, the world's choice), and every move of the time is one the schedules allow (`OutsideFact.Schedule`).
  */
final case class Timed(now: SymbolName, sleep: SymbolName, elapse: SymbolName)
