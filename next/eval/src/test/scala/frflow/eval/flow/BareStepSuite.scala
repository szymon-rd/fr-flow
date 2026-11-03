package frflow.eval.flow

import cats.effect.{IO, Ref}
import frflow.*
import whole.Theories

/** The step 13c re-review's R-N3: a program whose whole code is one operation's call, written bare
  * (`program { allHeld }`), is that call as a step, as `for xs <- allHeld yield xs` is.
  */
class BareStepSuite extends munit.FunSuite:
  test("a program written as one bare call is that call as a step: no crash, and no problem") {
    assertEquals(Theories.problems(BareStep.knowledge), Nil)
  }

  test("a program called bare as another's step is refused, a Problem, not a crash (R-N3)") {
    assertEquals(Theories.problems(BareStep.calling), List(frflow.core.analysis.Problem.StepNotOperation(
      frflow.core.name.DefName("againCode"), frflow.core.name.SymbolName("listed"))))
  }

object BareStep:
  val allHeld = Definition[Flow[List[BigInt]]]("the numbers held")
  object heldNums extends StateModel[List[BigInt]]("the numbers held"):
    allHeld.means(state.get)
  val listed = Definition[Flow[List[BigInt]]]("the numbers held, listed")
  val listedCode = program { allHeld }
  val heldOnly = Node.assumption("Nothing but the programs change the numbers held.")(heldNums.onlyCodeChanges)
  val heldOne = Node.assumption("One run at a time on the numbers held.")(heldNums.atomic)
  val listsHeld = Node.claim("Listing gives the numbers held.")(listed.result === heldNums.current)
    .assuming(heldOne)
  val again = Definition[Flow[List[BigInt]]]("the numbers held, listed again")
  val againCode = program { listed }
  val listsAgain = Node.claim("Listing again gives the numbers held.")(again.result === heldNums.current)
  val calling: FrModel = FrModel("BareStep")(listsHeld, listsAgain, heldOnly, heldOne)
    .implementProven(listed)(listedCode)
    .implementProven(again)(againCode)
    .implementTested(allHeld)(start = (xs: List[BigInt]) => Ref[IO].of(xs),
      observe = (r: Ref[IO, List[BigInt]]) => r.get)(r => Tuple1(r.get))
  val knowledge: FrModel = FrModel("BareStep")(listsHeld, heldOnly, heldOne)
    .implementProven(listed)(listedCode)
    .implementTested(allHeld)(start = (xs: List[BigInt]) => Ref[IO].of(xs),
      observe = (r: Ref[IO, List[BigInt]]) => r.get)(r => Tuple1(r.get))
