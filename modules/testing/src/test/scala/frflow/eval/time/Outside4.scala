package frflow.eval.time

import cats.effect.IO
import frflow.*

/** The step 13d fourth pass's P4-B2 probe, seeded: a claim of `always[Pos]` stronger than the assumption saying what
  * a `Pos` from outside meets. A `Pos(0)` from outside meets the assumption and is stored as 0: `posRule` (its
  * `outside` not proven) and `storesPositive` (resting on it) must stay unproven.
  */
object Outside4:
  final case class Pos(v: BigInt) derives LeanType

  val putB = Definition[BigInt => Flow[Unit]]("the box set")

  object box extends StateModel[BigInt]("a number"):
    putB.means(t => state.set(t))

  val store = Definition[Pos => Flow[Unit]]("a Pos's value put in the box")
  val storeCode = program { (p: Term[Pos]) => Flow.step(putB(p.v)) }

  val boxOne = Node.assumption("One run at a time on the box.")(box.atomic)
  val posFromOutside = Node.assumption("Every Pos from outside is not negative.")(always[Pos](p => p.v >= 0))
  val posRule = Node.claim("Every Pos is positive.")(always[Pos](p => p.v > 0)).assuming(posFromOutside)

  /** False of a Pos(0) from outside, which the assumption allows. */
  val storesPositive = Node.claim("Storing puts a positive number in the box.")(
    forall((p: Term[Pos]) => box.in(store(p).after) > 0)).assuming(boxOne, posFromOutside)

  val model: FrModel = FrModel("Outside4")(posRule, posFromOutside, storesPositive, boxOne)
    .implementProven(store)(storeCode)
    .implementTested(putB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(r => Tuple1((t: BigInt) => r.set(t)))
