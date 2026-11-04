package frflow.eval.time

import cats.effect.IO
import frflow.*

/** The step 13d fifth pass's P5-B1 probes, seeded: (a) a `Pos` made by tested plain Scala breaking the claimed rule
  * (`mkPos(0)`), which its test finds: `posRule` and `allPos` must stay unproven (`Kept(posRule)`); (b) a `Pos` nested
  * in an entry input, asked `outside` through the containing type; (c) a rule no `Pos` meets (`inhabited_` failing),
  * the assumptions consistent: `never` and `allBelow`, false of `mkPos(-1)`, must stay unproven (`Kept(never)`); (d)
  * that rule with no code, no maker and no test: its failing `inhabited_` alone keeps `noneBelow` from resting on it.
  */
object Sources5:
  final case class Pos(v: BigInt) derives LeanType
  final case class Wrap(p: Pos) derives LeanType

  val putB = Definition[BigInt => Flow[Unit]]("the box set")

  object box extends StateModel[BigInt]("a number"):
    putB.means(t => state.set(t))

  val boxOne = Node.assumption("One run at a time on the box.")(box.atomic)

  // (a) a Pos made by tested plain Scala, its value stored
  /** False: mkPos(-1) is a Pos its plain Scala makes. */
  val vOf = Definition[Pos => BigInt]("a Pos's number")
  val vOfCode = define { (p: Term[Pos]) => p.v }
  val allPos = Node.claim("Every Pos's number is above zero.")(forall((p: Term[Pos]) => vOf(p) >= 1))
  val mkPos = Definition[BigInt => Pos]("a Pos of a number, by plain Scala")
  val putMk = Definition[BigInt => Flow[Unit]]("a number's Pos stored")
  val putMkCode = program { (n: Term[BigInt]) => Flow.step(putB(vOf(mkPos(n)))) }
  val posRule = Node.claim("Every Pos is positive.")(always[Pos](p => p.v > 0))
  val mkStores = Node.claim("Storing a made Pos stores its number.")(
    forall((n: Term[BigInt]) => box.in(putMk(n).after) === vOf(mkPos(n)))).assuming(boxOne)

  val mkGives = Node.claim("A made Pos holds its number, when positive.")(
    forall((n: Term[BigInt]) => (n > 0) implies (mkPos(n).v === n)))
  val tested: FrModel = FrModel("Sources5a")(posRule, mkStores, mkGives, allPos, boxOne)
    .implementProven(putMk)(putMkCode)
    .implementProven(vOf)(vOfCode)
    .implementTested(mkPos)(_ => (n: BigInt) => Pos(n))
    .implementTested(putB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(r => Tuple1((t: BigInt) => r.set(t)))

  // (b) a Pos nested in an entry input, an assumption on the containing type only
  val putFirst = Definition[Wrap => Flow[Unit]]("the wrapped value stored")
  val putFirstCode = program { (w: Term[Wrap]) => Flow.step(putB(w.p.v)) }
  val boxesFromOutside = Node.assumption("Every Wrap from outside holds a value not negative.")(
    always[Wrap](w => w.p.v >= 0))
  val posFromOutsideB = Node.assumption("Every Pos from outside is not negative.")(always[Pos](p => p.v >= 0))
  val posRuleB = Node.claim("Every Pos is positive.")(always[Pos](p => p.v > 0)).assuming(posFromOutsideB)
  val firstStores = Node.claim("Storing a first item stores a positive number.")(
    forall((w: Term[Wrap]) => box.in(putFirst(w).after) > 0)).assuming(boxOne, boxesFromOutside, posFromOutsideB)

  val nested: FrModel = FrModel("Sources5b")(posRuleB, firstStores, boxesFromOutside, posFromOutsideB, boxOne)
    .implementProven(putFirst)(putFirstCode)
    .implementTested(putB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(r => Tuple1((t: BigInt) => r.set(t)))

  // (c) a rule no Pos meets, a tested maker of Pos: inhabited_ fails, the assumptions consistent
  /** False: mkPos(-1) is a Pos its plain Scala makes. */
  val allBelow = Node.claim("Every Pos's number is below minus five.")(forall((p: Term[Pos]) => vOf(p) < -5))
  val never = Node.claim("No Pos is ever made.")(always[Pos](p => p.v > 0 && p.v < 0))
  val mkNever = Node.claim("Storing a made Pos stores its number.")(
    forall((n: Term[BigInt]) => box.in(putMk(n).after) === vOf(mkPos(n)))).assuming(boxOne)

  val empty: FrModel = FrModel("Sources5c")(never, mkNever, mkGives, allBelow, boxOne)
    .implementProven(putMk)(putMkCode)
    .implementProven(vOf)(vOfCode)
    .implementTested(mkPos)(_ => (n: BigInt) => Pos(n))
    .implementTested(putB)(start = (n: BigInt) => IO.ref(n), observe = _.get)(r => Tuple1((t: BigInt) => r.set(t)))

  // (d) the same rule no Pos meets, with no code, no maker and no test: only its failing inhabited_ opens it
  val noneBelow = Node.claim("Every Pos's value is below minus five.")(forall((p: Term[Pos]) => p.v < -5))
  val vacant: FrModel = FrModel("Sources5d")(never, noneBelow)
