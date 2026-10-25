package frflow
package check

import frflow.fixtures.StockLaws

/** The relative monad's laws in Lean: each law's two sides are flow contracts with one post, both proven on the model
  * (in `StateM`), their examples evaluated there. End to end against Lean (see LeanLab).
  */
class LeanLawsSuite extends LeanLab:
  test("left unit, right unit and associativity: both sides of each proven of the same post on the model") {
    val r = workflow(StockLaws.kb).check()
    for n <- List(StockLaws.leftLhs, StockLaws.leftRhs, StockLaws.rightLhs, StockLaws.rightRhs, StockLaws.assocLhs, StockLaws.assocRhs) do
      val c = of(r, n.id)
      assertEquals(c.status.toString, "proven", c.obligations.map(o => o.name.lean -> o.status.toString))
      assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
  }
