package frflow.proof.layout.failing

import frflow.proof.layout.{Laid, LeanBuildSuite}
import frflow.proof.obligation.ObligationName

/** `Failing` built by Lean: programs that may fail run on the models' instance on `ExceptT String (StateM World)`,
  * the shelf's calls failing on the world's faults; what a run gives and what a failed one does are proven of
  * `file` and `check` (their `impl`), a failed run keeps what always holds (`cover_file`), `made_check` is of the
  * runs that succeed; and `spoil`, which fails leaving a booking ending before it starts, is caught: its `cover_` is
  * not proven, nor what it hands the shelf once the first call fails (`made_spoilIt_call_1`), of the claim and of the
  * assumption alike; nor is `fileWrong`'s false failure clause.
  */
class FailingLeanSuite extends LeanBuildSuite("failing", Laid(Failing.resolved, Map.empty, Nil),
  List("endsAfterStart", "fromOutside").flatMap(n => List(n -> ObligationName.Cover("spoil"),
    n -> ObligationName.Made("spoilIt_call_1"))) :+ ("fileWrong" -> ObligationName.Impl))
