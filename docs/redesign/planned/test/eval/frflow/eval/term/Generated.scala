package frflow.eval.term

import frflow.*
import frflow.dsl.term.Lift
import scala.util.Random

/** Random terms of the core language for the laws: every algebra's operations, binders over lists (`pairwise` too),
  * `allDistinct`, folds, `let`, a match over an enum, a record made and updated, defines called by name and passed as
  * functions. A body is a host function, called by each
  * interpreter as often as it likes, so it rebuilds its term from its own seed: the same term on every call.
  */
final class Generated(nums: List[Term[BigInt]], slots: List[Term[Slot]]):
  def bool(r: Random, depth: Int): Term[Boolean] = if depth <= 0 then num(r, 0) < num(r, 0) else r.nextInt(15) match
    case 0  => bool(r, depth - 1) && bool(r, depth - 1)
    case 1  => bool(r, depth - 1) || bool(r, depth - 1)
    case 2  => bool(r, depth - 1) implies bool(r, depth - 1)
    case 3  => !bool(r, depth - 1)
    case 4  => num(r, depth - 1) === num(r, depth - 1)
    case 5  => num(r, depth - 1) <= num(r, depth - 1)
    case 6  => val seed = r.nextLong(); Generated.slotList(r).forall(x => withSlot(x).bool(Random(seed), depth - 1))
    case 7  => val seed = r.nextLong(); Generated.numList(r).exists(x => withNum(x).bool(Random(seed), depth - 1))
    case 8  => Slots.within(slot(r, depth - 1), num(r, depth - 1))
    case 9  => Slots.sound(slot(r, depth - 1))
    case 10 => kinds(r, depth - 1)
    case 11 => val seed = r.nextLong()
               Generated.maybe(r).fold(bool(r, depth - 1))(x => withNum(x).bool(Random(seed), depth - 1))
    case 12 => val (s1, s2) = (r.nextLong(), r.nextLong())
               Generated.outcome(r).fold(e => withNum(e).bool(Random(s1), depth - 1),
                 a => withNum(a).bool(Random(s2), depth - 1))
    case 13 => relations(r, depth - 1)
    case _  => val seed = r.nextLong(); let(num(r, depth - 1))(x => withNum(x).bool(Random(seed), depth - 1))

  def num(r: Random, depth: Int): Term[BigInt] = if depth <= 0 then leaf(r) else r.nextInt(8) match
    case 0 => num(r, depth - 1) + num(r, depth - 1)
    case 1 => num(r, depth - 1) - num(r, depth - 1)
    case 2 => slot(r, depth - 1).start
    case 3 => when(bool(r, depth - 1))(num(r, depth - 1)).otherwise(num(r, depth - 1))
    case 4 => val seed = r.nextLong(); Generated.numList(r).filter(x => withNum(x).bool(Random(seed), depth - 1)).length
    case 5 => (num(r, depth - 1) :: Generated.numList(r) ++ Generated.numList(r)).length
    case 6 => val seed = r.nextLong()
              Generated.numList(r).foldLeft(num(r, depth - 1))((acc, x) => withNum(acc).withNum(x).num(Random(seed), 0))
    case _ => slot(r, depth - 1).updated(_.end, num(r, depth - 1)).end

  /** The list relations: no element twice, every pair in order, a define passed as a function. */
  private def relations(r: Random, depth: Int): Term[Boolean] = r.nextInt(3) match
    case 0 => Generated.numList(r).allDistinct
    case 1 => val seed = r.nextLong()
              Generated.numList(r).pairwise((a, b) => withNum(a).withNum(b).bool(Random(seed), depth))
    case _ => Generated.slotList(r).forall(Slots.sound)

  /** A match over an enum: each arm its own term over the case's fields. */
  private def kinds(r: Random, depth: Int): Term[Boolean] =
    val (s1, s2, s3) = (r.nextLong(), r.nextLong(), r.nextLong())
    Generated.kind(r).on[Kind.Room]((name, size) => (name === "Oak") || withNum(size).bool(Random(s1), depth))
      .on[Kind.Desk](n => withNum(n).bool(Random(s2), depth))
      .on(Kind.Closed)(bool(Random(s3), depth))

  private def leaf(r: Random): Term[BigInt] =
    if nums.nonEmpty && r.nextBoolean() then nums(r.nextInt(nums.size)) else Lift.constant(BigInt(r.nextInt(7) - 2))
  private def slot(r: Random, depth: Int): Term[Slot] = r.nextInt(3) match
    case 0 if slots.nonEmpty => slots(r.nextInt(slots.size))
    case 1                   => make[Slot](Lift.constant("Elm"), num(r, depth), num(r, depth))
    case _                   => Lift.constant(Generated.aSlot(r))
  private def withNum(x: Term[BigInt]) = Generated(x :: nums, slots)
  private def withSlot(x: Term[Slot]) = Generated(nums, x :: slots)

object Generated:
  def formula(seed: Long, depth: Int): Term[Boolean] = Generated(Nil, Nil).bool(Random(seed), depth)

  private def aSlot(r: Random): Slot =
    val start = BigInt(r.nextInt(5))
    Slot(if r.nextBoolean() then "Oak" else "Elm", start, start + r.nextInt(3) - 1)
  private def numList(r: Random): Term[List[BigInt]] = Lift.constant(List.fill(r.nextInt(4))(BigInt(r.nextInt(5))))
  private def slotList(r: Random): Term[List[Slot]] = Lift.constant(List.fill(r.nextInt(3))(aSlot(r)))
  private def maybe(r: Random): Term[Option[BigInt]] = Lift.constant(Option.when(r.nextBoolean())(BigInt(r.nextInt(5))))
  private def outcome(r: Random): Term[Either[BigInt, BigInt]] =
    Lift.constant(if r.nextBoolean() then Left(BigInt(r.nextInt(3))) else Right(BigInt(r.nextInt(3))))
  private def kind(r: Random): Term[Kind] = Lift.constant(r.nextInt(3) match
    case 0 => Kind.Room(if r.nextBoolean() then "Oak" else "Elm", BigInt(r.nextInt(9)))
    case 1 => Kind.Desk(BigInt(r.nextInt(4)))
    case _ => Kind.Closed)
