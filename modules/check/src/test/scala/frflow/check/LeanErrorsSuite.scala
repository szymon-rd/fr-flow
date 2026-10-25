package frflow
package check

import frflow.fixtures.Errors

/** Errors in Lean: flows that may fail run in `ExceptT E (StateM World)`, a failing boundary's call taking the next of
  * the world's faults; their contracts, what holds of a run that succeeds and of one that fails, proven for every
  * pattern of faults. End to end against Lean (see LeanLab).
  */
class LeanErrorsSuite extends LeanLab:
  test("raise, attempt, retry and guarantee: proven of the vault's model, for every pattern of faults") {
    val r = workflow(Errors.kb).check()
    for n <- List[Node[?]](Errors.withdrawContract, Errors.safelyContract, Errors.depositContract, Errors.restContract) do
      val c = of(r, n.id)
      assertEquals(c.status.toString, "proven", c.obligations.map(o => o.name.lean -> (o.status.toString, o.detail)))
      assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
  }
