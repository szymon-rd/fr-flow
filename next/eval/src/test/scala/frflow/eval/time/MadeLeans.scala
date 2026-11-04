package frflow.eval.time

import cats.effect.IO
import frflow.*

/** The step 13d third pass's R3-B1 probe, seeded: a value rule (`posMade`) whose `made_mk` takes a store rule
  * (`cellPositive`) on the world, while that rule is open (`zero` breaks it). In a real run zero, then mk, gives
  * Pos(0): `posMade` must stay unproven while `cellPositive` is (`Kept(cellPositive)`).
  */
object MadeLeans:
  final case class Pos(v: BigInt) derives LeanType

  val setC = Definition[BigInt => Flow[Unit]]("the cell set")
  val getC = Definition[Flow[BigInt]]("the cell read")

  object cell extends StateModel[BigInt]("a number"):
    setC.means(t => state.set(t))
    getC.means(state.get)

  val zero = Definition[Flow[Unit]]("the cell put to zero")
  val zeroCode = program { Flow.step(setC(0)) }
  val mk = Definition[Flow[Pos]]("a Pos made of the cell")
  val mkCode = program { for c <- Flow.step(getC) yield make[Pos](c) }

  val cellKept = Node.assumption("Only the code changes the cell.")(cell.onlyCodeChanges)
  val cellOne = Node.assumption("One run at a time on the cell.")(cell.atomic)
  val cellStarts = Node.assumption("The cell starts at one.")(cell.initially(c => c === 1))

  val cellPositive = Node.claim("The cell is always positive.")(always(cell)(c => c > 0))
    .assuming(cellKept, cellOne, cellStarts)
  val posMade = Node.claim("Every Pos is positive.")(always[Pos](p => p.v > 0))

  val zeroes = Node.claim("Zeroing puts the cell to zero.")(cell.in(zero.after) === 0).assuming(cellOne)
  val made = Node.claim("Making reads the cell.")(mk.result.v === cell.current).assuming(cellOne)

  val model: FrModel = FrModel("MadeLeans")(cellPositive, posMade, zeroes, made, cellKept, cellOne, cellStarts)
    .implementProven(zero)(zeroCode)
    .implementProven(mk)(mkCode)
    .implementTested(setC, getC)(start = (n: BigInt) => IO.ref(n), observe = _.get)(r =>
      ((t: BigInt) => r.set(t), r.get))
