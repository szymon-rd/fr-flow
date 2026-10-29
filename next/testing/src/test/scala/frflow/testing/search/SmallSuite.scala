package frflow.testing.search

import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary

/** The small values a witness search tries (`Small`), in order, so the search is deterministic. */
class SmallSuite extends munit.FunSuite:
  private val small = Small(Vocabulary(Nil, Nil, Nil, Nil, Nil))

  test("lists of none, one and two small elements, in order; a function has none") {
    val (f, t) = (Value.Bool(false), Value.Bool(true))
    assertEquals(small.of(Ty.ListOf(Ty.Bool)), List(Value.Many(Nil), Value.Many(List(f)), Value.Many(List(t)),
      Value.Many(List(f, f)), Value.Many(List(f, t)), Value.Many(List(t, f)), Value.Many(List(t, t))))
    assertEquals(small.of(Ty.FnOf(List(Ty.Bool), Ty.Bool)), Nil)
  }
