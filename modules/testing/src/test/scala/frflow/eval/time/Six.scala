package frflow.eval.time

import cats.effect.{IO, Ref}
import frflow.*
import frflow.eval.time.Sources5.{Pos, boxOne, mkPos, putB, putMk, putMkCode, vOf, vOfCode, allPos, posRule,
  mkStores}

/** The step 13d sixth pass's probes, seeded: (a) the tested maker's claim failing on its post first, so no test reports
  * the rule broken (P6-B1): `posRule` and `allPos` must stay unproven; (b) a store's plain Scala storing what its model
  * never would, the rule proven of the model (P6-B2): `nonNeg` red from its model's tests, `sumAtLeast` resting on it.
  */
object Six:
  /** Wrong for every n, so its tests fail on the post first. */
  val mkWrong = Node.claim("A made Pos holds one more than its number.")(forall((n: Term[BigInt]) =>
    mkPos(n).v === n + 1))
  val postFirst: FrModel = FrModel("SixA")(posRule, mkStores, mkWrong, allPos, boxOne)
    .defining(putMk.define(putMkCode))
    .defining(vOf.define(vOfCode))
    .defining(mkPos.defineTested(_ => (n: BigInt) => Pos(n)))
    .defining(defineOperations(putB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(
      r => Tuple1((t: BigInt) => r.set(t))))

  // (b)
  val setC = Declaration[BigInt => Flow[Unit]]("the cell set, never below zero")
  object cell extends StateModel[BigInt]("a number"):
    setC.means(t => state.set(when(t >= 0)(t).otherwise(0)))
  val put = Declaration[BigInt => Flow[Unit]]("a number put in the cell")
  val putCode = program { (n: Term[BigInt]) => Flow.step(setC(n)) }
  val cellKept = Node.assumption("Only the code changes the cell.")(cell.onlyCodeChanges)
  val cellOne = Node.assumption("One run at a time on the cell.")(cell.atomic)
  val cellStarts = Node.assumption("The cell starts at zero.")(cell.initially(c => c === 0))
  val nonNeg = Node.claim("The cell is never negative.")(always(cell)(c => c >= 0)).assuming(cellKept, cellOne,
    cellStarts)
  val puts = Node.claim("Putting a number not negative stores it.")(forall((n: Term[BigInt]) =>
    (n >= 0) implies (cell.in(put(n).after) === n))).assuming(cellOne)
  /** False of the plain Scala, which stores a negative number as it is. */
  val nowNonNeg = Node.claim("The cell is not negative now.")(cell.current >= 0)

  val setB = Declaration[BigInt => Flow[Unit]]("the other box set")
  object box2 extends StateModel[BigInt]("another number"):
    setB.means(t => state.set(t))
  val put2 = Declaration[BigInt => Flow[Unit]]("a number put in the other box")
  val put2Code = program { (n: Term[BigInt]) => Flow.step(setB(n)) }
  val box2One = Node.assumption("One run at a time on the other box.")(box2.atomic)
  /** Rests on nonNeg on the world it starts from, and runs on the other box only; false of the plain Scala cell. */
  val sumAtLeast = Node.claim("After putting a number in the other box, it and the cell add up to at least it.")(
    forall((n: Term[BigInt]) => box2.in(put2(n).after) + cell.current >= n)).assuming(box2One)

  /** The cell's plain Scala: it stores any number, a negative one too. */
  final class RawCell(r: Ref[IO, BigInt]):
    def set(t: BigInt): IO[Unit] = r.set(t)
    def held: IO[BigInt] = r.get

  val wrongScala: FrModel = FrModel("SixB")(nonNeg, puts, sumAtLeast, box2One, cellKept, cellOne,
      cellStarts)
    .defining(put.define(putCode))
    .defining(put2.define(put2Code))
    .defining(defineOperations(setB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(
      r => Tuple1((t: BigInt) => r.set(t))))
    .defining(defineOperations(setC)(start = (n: BigInt) => Ref[IO].of(n).map(RawCell(_)), observe = _.held)(c =>
      Tuple1(c.set)))

  /** The step 13d seventh pass's S7-N1, seeded: the same tested maker of a `Pos`, mentioned only by a claim saying what
    * a Declaration is, which no code is tested against: its Scala is never tried against the rule, so `posRule` must
    * stay open, and `aboveZero` resting on it.
    */
  val madeOf = Declaration[BigInt => Pos]("the Pos a number is made into")
  val madeSome = Node.claim("Every number is made into a Pos.")(forall((n: Term[BigInt]) =>
    madeOf(n).v === madeOf(n).v))
  val madeIs = Node.claim("A number is made into the Pos mkPos makes of it.")(forall((n: Term[BigInt]) =>
    madeOf(n) === mkPos(n))).refines(madeSome)
  val aboveZero = Node.claim("Every Pos holds a number above zero.")(forall((p: Term[Pos]) => p.v >= 1))
  val untried: FrModel = FrModel("SevenA")(posRule, aboveZero, madeSome, madeIs)
    .defining(mkPos.defineTested(_ => (n: BigInt) => Pos(n)))
