package frflow.project.program

import frflow.*

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
