package frflow.core.expr

import frflow.core.{Booking, Lang}
import frflow.core.expr.Tm.*
import frflow.core.name.{DefName, ModelName, SymbolName, TypeName}
import frflow.core.term.{Body, Bound, Sym}
import frflow.core.ty.Ty
import scala.collection.mutable
import scala.util.Random

/** Random terms over the algebras, each of a known type, made once from a seed: the laws' terms. Every random choice
  * is made before any interpreter runs the term, so each body gives the same term on every call. What a term names is
  * recorded as it is made, parts left to right, which is the order its IR meets them.
  */
final class Terms(seed: Long):
  import Terms.{fnTy, positive, stored}
  private val r = Random(seed)
  private val named = mutable.ListBuffer.empty[SymbolName]
  private val called = mutable.ListBuffer.empty[DefName]
  private val typed = mutable.ListBuffer.empty[TypeName]
  private val modelled = mutable.ListBuffer.empty[ModelName]

  /** What the terms made so far mention, as `Mentions` should say it. */
  def mentioned: Mentions = Mentions(named.toList.distinct, called.toList.distinct, typed.toList.distinct,
    Nil, modelled.toList.distinct)

  def bool(d: Int, k: Int): Tm[Boolean] = if d <= 0 then boolLeaf(k) else r.nextInt(20) match
    case 0  => and(bool(d - 1, k), bool(d - 1, k))
    case 1  => or(bool(d - 1, k), bool(d - 1, k))
    case 2  => implies(bool(d - 1, k), bool(d - 1, k))
    case 3  => not(bool(d - 1, k))
    case 4  => le(num(d - 1, k), num(d - 1, k))
    case 5  => Tm.eq(num(d - 1, k), num(d - 1, k))
    case 6  => forall(bool(d - 1, k + 1))
    case 7  => exists(bool(d - 1, k + 1))
    case 8  => all(nums(d - 1, k), bool(d - 1, k + 1))
    case 9  => pairwise(nums(d - 1, k), bool(d - 1, k + 2))
    case 10 => nodup(nums(d - 1, k))
    case 11 => cond(bool(d - 1, k), bool(d - 1, k), bool(d - 1, k))
    case 12 => let(num(d - 1, k), bool(d - 1, k + 1))
    case 13 => foldOption(opt(d - 1, k), bool(d - 1, k), bool(d - 1, k + 1))
    case 14 => app(note(called, positive.name)(define(positive)), num(d - 1, k))
    case 15 => app(symbol[BigInt => Boolean]("p", fnTy), num(d - 1, k))
    case 16 => app(fn(d - 1, k), num(d - 1, k))
    case 17 => held(d, k)
    case _  => Tm.eq(booking(d - 1, k), booking(d - 1, k))

  /** Whether a list, an option or a set holds a value, or one meeting a rule. */
  def held(d: Int, k: Int): Tm[Boolean] = r.nextInt(8) match
    case 0 => contains(nums(d - 1, k), num(d - 1, k))
    case 1 => isEmpty(nums(d - 1, k))
    case 2 => optionAll(opt(d - 1, k), bool(d - 1, k + 1))
    case 3 => optionAny(opt(d - 1, k), bool(d - 1, k + 1))
    case 4 => isDefined(opt(d - 1, k))
    case _ => member(set(d - 1, k), num(d - 1, k))

  def num(d: Int, k: Int): Tm[BigInt] = if d <= 0 then numLeaf(k) else r.nextInt(12) match
    case 0 => add(num(d - 1, k), num(d - 1, k))
    case 1 => sub(num(d - 1, k), num(d - 1, k))
    case 2 => cond(bool(d - 1, k), num(d - 1, k), num(d - 1, k))
    case 3 => length(nums(d - 1, k))
    case 4 => end(read(d - 1, k))
    case 5 => foldLeft(nums(d - 1, k), num(d - 1, k), num(d - 1, k + 2))
    case 6 => let(num(d - 1, k), num(d - 1, k + 1))
    case 7 => getOrElse(opt(d - 1, k), num(d - 1, k))
    case 8 | 11 => getOrElseAt(table(d - 1, k), num(d - 1, k), num(d - 1, k))
    case 9 => second(num(d - 1, k), num(d - 1, k))
    case _ => foldOption(opt(d - 1, k), num(d - 1, k), num(d - 1, k + 1))

  def nums(d: Int, k: Int): Tm[List[BigInt]] = if d <= 0 then numsLeaf else r.nextInt(7) match
    case 0 => cons(num(d - 1, k), nums(d - 1, k))
    case 1 => append(nums(d - 1, k), nums(d - 1, k))
    case 2 => filter(nums(d - 1, k), bool(d - 1, k + 1))
    case 3 => map(nums(d - 1, k), num(d - 1, k + 1))
    case 4 => flatMap(nums(d - 1, k), nums(d - 1, k + 1))
    case 5 => firsts(nums(d - 1, k), nums(d - 1, k))
    case _ => numsLeaf

  def opt(d: Int, k: Int): Tm[Option[BigInt]] = r.nextInt(5) match
    case 0 => some(num(d - 1, k))
    case 1 => none
    case 2 => find(nums(d - 1, k), bool(d - 1, k + 1))
    case 3 => get(table(d - 1, k), num(d - 1, k))
    case _ => symbol("o", Ty.OptionOf(Lang.big))

  def set(d: Int, k: Int): Tm[Set[BigInt]] = if d <= 0 then symbol("s", Ty.SetOf(Lang.big)) else r.nextInt(5) match
    case 0 | 1 => incl(set(d - 1, k), num(d - 1, k))
    case 2 | 3 => union(set(d - 1, k), set(d - 1, k))
    case _ => symbol("s", Ty.SetOf(Lang.big))

  /** A map of numbers to numbers. */
  def table(d: Int, k: Int): Tm[Map[BigInt, BigInt]] =
    if d <= 0 || r.nextBoolean() then symbol("m", Ty.MapOf(Lang.big, Lang.big))
    else updated(table(d - 1, k), num(d - 1, k), num(d - 1, k))

  def booking(d: Int, k: Int): Tm[Booking] =
    if r.nextBoolean() then note(typed, Booking.name)(make(num(d - 1, k), num(d - 1, k))) else read(d, k)

  /** A booking not made on the spot, so a field read stays one in the IR. */
  def read(d: Int, k: Int): Tm[Booking] =
    if d <= 0 || r.nextBoolean() then note(typed, Booking.name)(symbol("slot", Booking.ty))
    else copy(booking(d - 1, k), num(d - 1, k))

  def fn(d: Int, k: Int): Tm[BigInt => Boolean] = lam(bool(d - 1, k + 1))

  private def boolLeaf(k: Int): Tm[Boolean] = r.nextInt(3) match
    case 0 => Tm.bool(r.nextBoolean())
    case 1 => note(modelled, stored.model)(outside(stored))
    case _ => lt(numLeaf(k), numLeaf(k))

  private def numLeaf(k: Int): Tm[BigInt] = r.nextInt(3) match
    case 0 if k > 0 => variable(r.nextInt(k))
    case 1          => symbol("k", Lang.big)
    case _          => Tm.num(r.nextInt(5) - 2)

  private def numsLeaf: Tm[List[BigInt]] = r.nextInt(3) match
    case 0 => nil
    case 1 => symbol("xs", Ty.ListOf(Lang.big))
    case _ => Tm.nums(List.fill(r.nextInt(3))(BigInt(r.nextInt(4))))

  private def symbol[A](name: String, ty: Ty): Tm[A] = note(named, SymbolName(name))(param[A](name, ty))

  /** `t`, recording that it names `a` (before its parts are made). */
  private def note[A, B](names: mutable.ListBuffer[A], a: A)(t: => Tm[B]): Tm[B] =
    names.append(a)
    t

object Terms:
  val fnTy: Ty = Ty.FnOf(List(Lang.big), Ty.Bool)
  val stored: OutsideFact.Atomic = OutsideFact.Atomic(ModelName("stored"))
  val positive: Body[BigInt => Boolean] = Body(DefName("positive"), fnTy, [T[_]] => (s: Sym[T]) =>
    s.lam(Bound[BigInt]("n", Lang.big))(n => s.lt(Lang(s).num(0), n)))
