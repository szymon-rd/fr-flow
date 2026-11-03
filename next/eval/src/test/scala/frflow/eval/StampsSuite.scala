package frflow.eval

import frflow.eval.flow.Stamps
import whole.Theories

/** The stamps (owner §47) as written: valid, both what holds as time passes and its seeded bugs. */
class StampsSuite extends munit.FunSuite:
  test("the stamps are valid as written, what holds and what is seeded") {
    assertEquals(List(Stamps.kept, Stamps.seeded, Stamps.scheduled, Stamps.circling, time.Lapse.lapse,
      time.Extend.model, time.Frozen.model).map(Theories.problems), List.fill(7)(Nil))
  }
