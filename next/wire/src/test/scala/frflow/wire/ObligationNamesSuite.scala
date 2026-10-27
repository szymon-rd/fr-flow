package frflow.wire

import frflow.proof.lean.lower.LowerObligation
import frflow.wire.check.ObligationNames
import org.scalacheck.Prop

/** An obligation is written as Lean names its theorem, and read back from that name alone. */
class ObligationNamesSuite extends munit.ScalaCheckSuite:
  property("an obligation's name is its theorem's name in Lean") {
    Prop.forAll(CheckDraws.obligation)(o => assertEquals(ObligationNames.text(o), LowerObligation.name(o).text))
  }

  property("an obligation reads back from its name") {
    Prop.forAll(CheckDraws.obligation)(o => assertEquals(ObligationNames.obligation(ObligationNames.text(o)), Some(o)))
  }

  test("a name no obligation has does not read") {
    List("", "proof", "restates_x", "commute_", "satisfiable_two_Root", "consistent_1.5").foreach(s =>
      assertEquals(ObligationNames.obligation(s), None, s))
  }
