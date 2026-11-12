package frflow.eval.time

import cats.effect.IO
import frflow.*

/** The step 13d fourth pass's P4-B1 probe, seeded: a rule whose `start_` fails (y starts at one), and a claim resting
  * on it. At the start, where y is one, zeroing changes y: `yIsZero` must stay unproven while `yZero` is open
  * (`Kept(yZero)`).
  */
object Starts4:
  val setY = Declaration[BigInt => Flow[Unit]]("y set")

  object ys extends StateModel[BigInt]("y"):
    setY.means(t => state.set(t))

  val zeroY = Declaration[Flow[Unit]]("y put to zero")
  val zeroYCode = program { Flow.step(setY(0)) }

  val yKept = Node.assumption("Only the code changes y.")(ys.onlyCodeChanges)
  val yOne = Node.assumption("One run at a time on y.")(ys.atomic)
  val yStarts = Node.assumption("y starts at one.")(ys.initially(y => y === 1))

  val yZero = Node.claim("y is always zero.")(always(ys)(y => y === 0)).assuming(yKept, yOne, yStarts)
  /** False at the start, where y is one. */
  val yIsZero = Node.claim("Zeroing leaves y as it was.")(ys.in(zeroY.after) === ys.current).assuming(yOne)
  val zeroes = Node.claim("Zeroing puts y to zero.")(ys.in(zeroY.after) === 0).assuming(yOne)

  val model: FrModel = FrModel("Starts4")(yZero, yIsZero, yKept, yOne, yStarts)
    .defining(zeroY.define(zeroYCode))
    .defining(defineOperations(setY)(start = (n: BigInt) => IO.ref(n), observe = _.get)(
      r => Tuple1((t: BigInt) => r.set(t))))
