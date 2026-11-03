package frflow.eval.flow

import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.*

import InterferenceProbe.*

/** The step 13 re-review's probes in production (RB1, RB2): the sides' steps interleave, so the claims Lean would
  * prove of them read in turn are false of the code (`AtOnceLeanSuite` keeps them unproven). Each interleaving is
  * made by the Scala waiting on the other side's steps, not by pauses, so a loaded machine runs the same one.
  */
class InterferenceProbeSuite extends munit.FunSuite:
  test("RB1: the set wins, and the copy, run until it was cancelled, read the new number into b") {
    (for
      (a, b) <- racing
      run    <- raced.running[cats.effect.IO](aModel := a, bModel := b)
      out    <- run(racerCode)
      av     <- a.value
      bv     <- b.value
    yield assertEquals((out, av, bv), (Left(()), BigInt(1), BigInt(1)))).unsafeRunSync()
  }

  test("RB2: two bumps at once, each a read then a set, lose one: a is up by one") {
    (for
      a   <- A.bothRead(0)
      b   <- B.holding(0)
      run <- bumped.running[cats.effect.IO](aModel := a, bModel := b)
      _   <- run(twiceCode)
      av  <- a.value
    yield assertEquals(av, BigInt(1))).unsafeRunSync()
  }

  test("two sets at once on models apart: both land") {
    (for
      a   <- A.holding(0)
      b   <- B.holding(0)
      run <- separate.running[cats.effect.IO](aModel := a, bModel := b)
      _   <- run(apartCode)
      ab  <- (a.value, b.value).tupled
    yield assertEquals(ab, (BigInt(1), BigInt(2)))).unsafeRunSync()
  }
