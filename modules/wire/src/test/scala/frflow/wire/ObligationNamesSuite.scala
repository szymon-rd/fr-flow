package frflow.wire

import frflow.wire.sample.*
import frflow.wire.check.ObligationNames
import org.scalacheck.Prop

/** An obligation is written as Lean names its theorem (`LowerObligation.name`), and read back from that name alone. */
class ObligationNamesSuite extends munit.ScalaCheckSuite:
  property("an obligation reads back from its name") {
    Prop.forAll(CheckDraws.obligation)(o => assertEquals(ObligationNames.obligation(ObligationNames.text(o)), Some(o)))
  }

  test("a name no obligation has does not read") {
    List("", "proof", "restates_x", "commute_", "satisfiable_two_Root", "consistent_1.5").foreach(s =>
      assertEquals(ObligationNames.obligation(s), None, s))
  }
