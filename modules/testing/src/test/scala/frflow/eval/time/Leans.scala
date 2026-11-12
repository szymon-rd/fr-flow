package frflow.eval.time

import frflow.*

/** The step 13d re-review's R-B1 probe, seeded: a rule (`yZero`) whose `cover_copy` takes another rule (`xZero`) on
  * the world before, while `xZero` itself is not kept (`bump` breaks it). In a real run bump, then copy, leaves y = 1:
  * `yZero` must stay unproven while `xZero` is (`Kept(xZero)`). Found where time passing left a port's rule open.
  */
object Leans:
  val setX = Declaration[BigInt => Flow[Unit]]("x set")
  val getX = Declaration[Flow[BigInt]]("x read")
  val setY = Declaration[BigInt => Flow[Unit]]("y set")

  object xs extends StateModel[BigInt]("x"):
    setX.means(t => state.set(t))
    getX.means(state.get)

  object ys extends StateModel[BigInt]("y"):
    setY.means(t => state.set(t))

  val bump = Declaration[Flow[Unit]]("x put to one")
  val bumpCode = program { Flow.step(setX(1)) }
  val copy = Declaration[Flow[Unit]]("y put to x")
  val copyCode = program {
    for
      x <- Flow.step(getX)
      _ <- Flow.step(setY(x))
    yield Flow.done }

  val xKept = Node.assumption("Only the code changes x.")(xs.onlyCodeChanges)
  val xOne = Node.assumption("One run at a time on x.")(xs.atomic)
  val xStarts = Node.assumption("x starts at zero.")(xs.initially(x => x === 0))
  val yKept = Node.assumption("Only the code changes y.")(ys.onlyCodeChanges)
  val yOne = Node.assumption("One run at a time on y.")(ys.atomic)
  val yStarts = Node.assumption("y starts at zero.")(ys.initially(y => y === 0))

  val xZero = Node.claim("x is always zero.")(always(xs)(x => x === 0)).assuming(xKept, xOne, xStarts)
  val yZero = Node.claim("y is always zero.")(always(ys)(y => y === 0)).assuming(yKept, yOne, yStarts)

  val copies = Node.claim("Copying puts y to x.")(ys.in(copy.after) === xs.current).assuming(xOne, yOne)
  val bumps = Node.claim("Bumping puts x to one.")(xs.in(bump.after) === 1).assuming(xOne)

  val model: FrModel = FrModel("Leans")(xZero, yZero, copies, bumps, xKept, xOne, xStarts, yKept, yOne, yStarts)
    .defining(bump.define(bumpCode))
    .defining(copy.define(copyCode))
    .defining(defineOperations(setX, getX)(start = (n: BigInt) => cats.effect.IO.ref(n), observe = _.get)(r =>
      ((t: BigInt) => r.set(t), r.get)))
    .defining(defineOperations(setY)(start = (n: BigInt) => cats.effect.IO.ref(n), observe = _.get)(r =>
      Tuple1((t: BigInt) => r.set(t))))
