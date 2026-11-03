package frflow.eval.flow

import whole.Theories

/** The stamps (owner §47) as written: valid, both what holds as time passes and its seeded bugs. */
class StampsSuite extends munit.FunSuite:
  test("the stamps are valid as written, what holds and what is seeded") {
    assertEquals(List(Stamps.kept, Stamps.seeded).map(Theories.problems), List(Nil, Nil))
  }
