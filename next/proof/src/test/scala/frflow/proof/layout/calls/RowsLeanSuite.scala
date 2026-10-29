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
