package frflow.proof.layout.failing

import frflow.proof.layout.{Laid, LeanBuildSuite}
import frflow.proof.obligation.ObligationName

/** `Failing` built by Lean: programs that may fail run on the models' instance on `ExceptT String (StateM World)`,
  * the shelf's calls failing on the world's faults; what a run gives and what a failed one does are proven of
  * `file` and `check` (their `impl`), a failed run keeps what always holds (`cover_file`), `made_check` is of the
  * runs that succeed; and `spoil`, which fails leaving a booking ending before it starts, is caught: its `cover_` is
  * not proven, nor what it hands the shelf once the first call fails (`made_spoilIt_call_1`), of the claim and of the
  * assumption alike; nor is `fileWrong`'s false failure clause. Nor do `twice`'s two filings at once commute
  * (`commute_0`): each given its own faults (the step 13 review's G3), one failing while the other lands leaves a
  * world the other order does not, so the in-turn reading does not stand for a run of them at once (one list of faults
  * hid it, the first call failing in either order).
  */
class FailingLeanSuite extends LeanBuildSuite("failing", Laid(Failing.resolved, Map.empty, Nil),
  List("endsAfterStart", "fromOutside").flatMap(n => List(n -> ObligationName.Cover("spoil"),
    n -> ObligationName.Made("spoilIt_call_1"))) :+ ("fileWrong" -> ObligationName.Impl) :+
    ("twiceRuns" -> ObligationName.Commute(0)))
