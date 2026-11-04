package frflow.eval

import frflow.eval.flow.Stamps
import whole.Theories

/** The stamps (owner §47) as written: valid, both what holds as time passes and its seeded bugs. */
class StampsSuite extends munit.FunSuite:
  test("the stamps are valid as written, what holds and what is seeded") {
    assertEquals(List(Stamps.kept, Stamps.seeded, Stamps.scheduled, Stamps.circling, time.Lapse.lapse,
      time.Extend.model, time.Frozen.model, time.Late.model, time.Leans.model, time.Unwritten.model,
      time.MadeLeans.model, time.Starts4.model, time.Outside4.model, time.Sources5.tested, time.Sources5.nested,
      time.Sources5.empty, time.Sources5.vacant, time.Six.postFirst, time.Six.wrongScala,
      time.Six.untried).map(Theories.problems), List.fill(20)(Nil))
  }
