package whole

import frflow.*

/** Seeded models from the step 12 review, each a bug FrFlow must not let through. */
object Seeded:
  /** Two assumptions pinning the provided `n` apart (`n = 0` through `d1`, `n = 1` through `d2`): one group, since
    * they must hold together, and no witness meets it.
    */
  object TwoPins:
    val n = Definition[BigInt]("a value provided where the code runs")
    val d1 = Declaration[BigInt => BigInt]("one reading of n")
    val d2 = Declaration[BigInt => BigInt]("another reading of n")

    val five = Node.claim("n is five.")(n === (5: Term[BigInt]))
    val nIsD1 = Node.assumption("n is d1.")(n === d1(0)).refines(five)
    val d1IsZero = Node.assumption("d1 is zero.")(forall((x: Term[BigInt]) => d1(x) === (0: Term[BigInt])))
      .refines(five)
    val nIsD2 = Node.assumption("n is d2.")(n === d2(0)).refines(five)
    val d2IsOne = Node.assumption("d2 is one.")(forall((x: Term[BigInt]) => d2(x) === (1: Term[BigInt])))
      .refines(five)

    val knowledge = FrModel("TwoPins")(five, nIsD1, d1IsZero, nIsD2, d2IsOne).implementProvided(n)

  /** Assumptions with no open value, each pinning the provided `n` apart: a group of their own. */
  object Closed:
    val n = Definition[BigInt]("a value provided where the code runs")
    val five = Node.claim("n is five.")(n === (5: Term[BigInt]))
    val nIsZero = Node.assumption("n is zero.")(n === (0: Term[BigInt])).refines(five)
    val nIsOne = Node.assumption("n is one.")(n === (1: Term[BigInt])).refines(five)
    val knowledge = FrModel("Closed")(five, nIsZero, nIsOne).implementProvided(n)

  /** `inner`'s code reached only through `outer`'s: with the real code `holdsIs` and `holdsOne` contradict each
    * other (`twice` leaves the bag two long and holding the item), so no proof may show their group consistent.
    */
  object Hidden:
    val inner = Definition[(Bag, BigInt) => Bag]("puts an item in a bag")
    val outer = Definition[(Bag, BigInt) => Bag]("puts an item in a bag, through inner")
    val holds = Declaration[(Bag, BigInt) => Boolean]("whether putting the item in the bag leaves it there")
    val twice = define { (b: Term[Bag], x: Term[BigInt]) => make[Bag](b.items :+ x :+ x) }
    val through = define { (b: Term[Bag], x: Term[BigInt]) => inner(b, x) }

    val purpose = Node.claim("Putting an item in a bag never leaves it there.")(
      forall((b: Term[Bag], x: Term[BigInt]) => !holds(b, x)))
    val seen = Node.claim("What holds is in the bag.")(
      forall((b: Term[Bag], x: Term[BigInt]) => holds(b, x) implies outer(b, x).items.contains(x)))
    val holdsIs = Node.claim("Holding is being in the bag outer makes.")(
      forall((b: Term[Bag], x: Term[BigInt]) => holds(b, x) === outer(b, x).items.contains(x))).refines(seen)
    val holdsOne = Node.claim("Holding is the bag outer makes holding one item.")(
      forall((b: Term[Bag], x: Term[BigInt]) => holds(b, x) === (outer(b, x).items.length === (1: Term[BigInt]))))
      .refines(purpose)
    val outerLong = Node.claim("outer's bag holds two items or more.")(
      forall((b: Term[Bag], x: Term[BigInt]) => outer(b, x).items.length >= (2: Term[BigInt]))).refines(purpose)
    val innerLong = Node.claim("inner's bag holds two items or more.")(
      forall((b: Term[Bag], x: Term[BigInt]) => inner(b, x).items.length >= (2: Term[BigInt]))).refines(outerLong)

    val knowledge = FrModel("Hidden")(purpose, seen, holdsIs, holdsOne, outerLong, innerLong)
      .implementProven(inner)(twice).implementProven(outer)(through)

    /** The proof the review wrote: `inner` chosen as a bag of the item alone, `holds` as always. */
    val proof: String = """import FrFlowGen.Hidden.Whole.Spec

set_option autoImplicit false
noncomputable section
open Classical

namespace Hidden.Whole.Proofs

theorem consistent_0 : Obl.consistent_0 := by
  refine ⟨fun _ _ => True, fun _ x => Bag.mk [x], ?_, ?_⟩
  · intro b x
    simp [Hidden.through]
  · intro b x
    simp [Hidden.through]

end Hidden.Whole.Proofs
"""

final case class Bag(items: List[BigInt]) derives LeanType
final case class Box(items: List[BigInt]) derives LeanType

/** A step over what makers make (`top`, from `holdsIs` and `outerAdds`), `outer` the maker its parts are about: the
  * maker breaking the rule `noDups` itself (`Direct`) or through `inner`, which it calls (`Indirect`).
  */
final class Makers(name: String, breaksInner: Boolean):
  val distinct = define { (b: Term[Box]) => b.items.pairwise((x, y) => x =!= y) }
  val boxesFromOutside = Node.assumption("Boxes from outside hold each item once.")(always[Box](b => distinct(b)))
  val inner = Definition[(Box, BigInt) => Box]("puts an item in a box")
  val outer = Definition[(Box, BigInt) => Box]("puts an item in a box, through inner")
  val holds = Declaration[(Box, BigInt) => Boolean]("whether putting the item in the box leaves it there")
  val good = define { (b: Term[Box], x: Term[BigInt]) =>
    when(b.items.contains(x))(b).otherwise(make[Box](b.items :+ x)) }
  val twice = define { (b: Term[Box], x: Term[BigInt]) => make[Box](b.items :+ x :+ x) }
  val through = define { (b: Term[Box], x: Term[BigInt]) => inner(b, x) }
  val again = define { (b: Term[Box], x: Term[BigInt]) => make[Box](inner(b, x).items :+ x) }

  val purpose = Node.claim("Putting an item in a box leaves it there, as the purpose.")(
    forall((b: Term[Box], x: Term[BigInt]) => holds(b, x))).assuming(boxesFromOutside)
  val top = Node.claim("Putting an item in a box leaves it there.")(
    forall((b: Term[Box], x: Term[BigInt]) => holds(b, x))).refines(purpose).assuming(boxesFromOutside)
  val holdsIs = Node.claim("Holding is being in the box outer makes.")(
    forall((b: Term[Box], x: Term[BigInt]) => holds(b, x) === outer(b, x).items.contains(x))).refines(top)
  val outerAdds = Node.claim("outer's box holds the item.")(
    forall((b: Term[Box], x: Term[BigInt]) => outer(b, x).items.contains(x))).refines(top)
    .assuming(boxesFromOutside)
  val innerAdds = Node.claim("inner's box holds the item.")(
    forall((b: Term[Box], x: Term[BigInt]) => inner(b, x).items.contains(x))).refines(outerAdds)
    .assuming(boxesFromOutside)
  val noDups = Node.claim("Every box made holds each item once.")(always[Box](b => distinct(b)))
    .refines(top).assuming(boxesFromOutside)

  val knowledge = FrModel(name)(purpose, top, holdsIs, outerAdds, innerAdds, noDups, boxesFromOutside)
    .implementProven(inner)(if breaksInner then twice else good)
    .implementProven(outer)(if breaksInner then through else again)
