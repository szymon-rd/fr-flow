package frflow.eval

import frflow.eval.flow.Stamps
import whole.Theories

/** The stamps (owner §47) as written: valid, both what holds as time passes and its seeded bugs. */
class StampsSuite extends munit.FunSuite:
  test("the stamps are valid as written, what holds and what is seeded") {
    assertEquals(List(Stamps.kept, Stamps.seeded, Stamps.scheduled).map(Theories.problems), List(Nil, Nil, Nil))
  }
