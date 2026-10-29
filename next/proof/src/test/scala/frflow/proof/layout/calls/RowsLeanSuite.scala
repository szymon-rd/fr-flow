package frflow.proof.layout.calls

import frflow.proof.layout.{Laid, LeanBuildSuite}
import frflow.proof.obligation.ObligationName

/** `Rows` built by Lean (owner §37): the job adding a key only when the rows do not hold it hands `storeAbout` rows
  * holding each key once, on every path, proven; every other obligation too.
  */
class RowsLeanSuite extends LeanBuildSuite("rows", Laid(Rows.resolved(Rows.once), Map.empty, Nil), Nil)

/** The seeded bug: the job adding the key whatever the rows hold stores a duplicate where they hold it, and what it
  * hands `storeAbout` is not proven to hold each key once (`made_expireIt_call_0` stays open, of the claim and of
  * the assumption alike).
  */
class RowsBugLeanSuite extends LeanBuildSuite("rows-bug", Laid(Rows.resolved(Rows.duplicates), Map.empty, Nil),
  List("onePerKey", "rowsFromOutside").map(_ -> ObligationName.Made("expireIt_call_0")))

/** The same bug through a branch's result and through a loop's element (review 11b, B1): nothing is assumed of a
  * value the job binds, so neither is proven.
  */
class RowsViaBranchLeanSuite extends LeanBuildSuite("rows-via-branch", Laid(Rows.resolved(Rows.viaBranch), Map.empty,
  Nil), List("onePerKey", "rowsFromOutside").map(_ -> ObligationName.Made("expireIt_call_0")))

class RowsViaLoopLeanSuite extends LeanBuildSuite("rows-via-loop", Laid(Rows.resolved(Rows.viaLoop), Map.empty, Nil),
  List("onePerKey", "rowsFromOutside").map(_ -> ObligationName.Made("expireIt_call_0")))

/** `Handed` built by Lean (review 11b, B1 and B2): what proven code hands plain Scala through a define written on the
  * spot, through another Definition's proven code, and from a tested function's result, is not proven to meet the
  * rule; `helper`'s own call, of an input from outside, is.
  */
class HandedLeanSuite extends LeanBuildSuite("handed", Laid(Handed.resolved, Map.empty, Nil),
  for
    n    <- List("endsAfterStart", "fromOutside")
    call <- List("spotCode_call_0", "definitionCode_call_0", "eachCode_call_1")
  yield n -> ObligationName.Made(call))
