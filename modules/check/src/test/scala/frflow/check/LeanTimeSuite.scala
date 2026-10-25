package frflow
package check

import frflow.fixtures.Timing

/** Time in Lean: the clock's state in the world, a sleep moving it on by the time asked and a delay it may add; flows
  * over it proven for every start time and every delay. End to end against Lean (see LeanLab).
  */
class LeanTimeSuite extends LeanLab:
  test("waitUntil, timeout and two sleeps: proven of the clock's model, for every start and every delay") {
    val r = workflow(Timing.kb).check()
    for n <- List(Timing.waitUntilContract, Timing.timeoutContract, Timing.twoNightsContract) do
      val c = of(r, n.id)
      assertEquals(c.status.toString, "proven", c.obligations.map(o => o.name.lean -> (o.status.toString, o.detail)))
      assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
  }
