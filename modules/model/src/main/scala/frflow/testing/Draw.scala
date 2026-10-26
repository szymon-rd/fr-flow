package frflow
package testing

import frflow.types.Shape
import java.util.SplittableRandom
import scala.collection.mutable

/** One generated case: its random numbers, its size, and the values it has made of each type, so that the token a
  * table holds and the token asked about are often the same.
  */
final class Draw private[frflow] (rnd: SplittableRandom, val size: Int, plan: Plan):
  private val pools = mutable.Map.empty[String, mutable.ArrayBuffer[Any]]
  /** How many draws a value of a type with invariants gets before the case is given up. */
  private val Tries = 20
  private var depth = 0
  def below(n: Int): Int = if n <= 1 then 0 else rnd.nextInt(n)
  def chance(p: Double): Boolean = rnd.nextDouble() < p
  /** How many elements a list gets: fewer the deeper it is. */
  def length: Int = below(size / (depth + 1) + 2)

  /** A value of `t` that holds the invariants of its type: drawn again (a few times) when one does not, or when its
    * constructor refuses the fields drawn.
    */
  private[frflow] def value(t: LeanType[?]): Any =
    @scala.annotation.tailrec def attempt(left: Int): Any =
      val drawn =
        try Some(if left < Tries then retrying(once(t)) else once(t))
        catch
          case e: CannotGenerate                       => throw e
          case _: IllegalArgumentException if left > 1 => None
      drawn match
        case Some(v) if scala.util.Try(plan.holds(t)(v)).getOrElse(true) => v
        case _ if left > 1 => attempt(left - 1)
        case _             => throw CannotGenerate(s"${Types.scala(t)}: no value drawn holds what always holds of it")
    attempt(Tries)

  // Drawn again: fresh values all the way down, not the ones pooled, which may be why the first did not hold.
  private var retries = 0
  private def retrying[A](f: => A): A =
    retries += 1
    try f
    finally retries -= 1

  private def once(t: LeanType[?]): Any =
    val seeds = plan.seedsOf(t)
    plan.customFor(t) match
      case Some(g) if chance(0.75) || plan.only(t) && (seeds.isEmpty || chance(0.8)) => g.draw(this)
      case Some(_) if plan.only(t) => seeds(below(seeds.size))
      case _ =>
        val k = plan.key(t)
        lazy val pool = pools.getOrElseUpdate(k, mutable.ArrayBuffer.empty)
        if seeds.nonEmpty && chance(0.15) then seeds(below(seeds.size))
        else if seeds.nonEmpty && chance(0.1) then
          val s = seeds(below(seeds.size))
          (if plan.holdsOnly(t) then Nil else Probes.near(s, plan.numbers)) match
            case Nil  => s
            case near => near(below(near.size))
        else if pooled(t) && pool.nonEmpty && retries == 0 && chance(0.6) then pool(below(pool.size))
        else
          val v = fresh(t)
          // Only a value that holds what always holds of its type is drawn again.
          if pooled(t) && pool.size < 4 && scala.util.Try(plan.holds(t)(v)).getOrElse(true) then pool += v
          v

  private def pooled(t: LeanType[?]): Boolean = t.shape match
    case Shape.Str | Shape.Num(_) | Shape.Opq(_) | Shape.Data(_) => true
    case _ => false

  private def nested[A](f: => A): A =
    depth += 1
    try f
    finally depth -= 1

  private def number: BigInt =
    if chance(0.3) then BigInt(below(3) - 1)
    else if plan.numbers.nonEmpty && chance(0.4) then plan.numbers(below(plan.numbers.size)) + (below(3) - 1)
    else BigInt(below(20 * size + 1) - 10 * size)

  private def string: String =
    if chance(0.2) then "" else List.fill(below(4) + 1)("ab1"(below(3))).mkString

  private def default(r: LeanType[?]): Any = r.shape match
    case Shape.OptionOf(_) => None
    case Shape.Prop        => false
    case Shape.ListOf(_)   => Nil
    case _                 => value(r)

  private def fresh(t: LeanType[?]): Any = t.shape match
    case Shape.Prop        => chance(0.5)
    case Shape.Num(k)      => k.of(number)
    case Shape.Str         => string
    case Shape.UnitT       => ()
    case Shape.ListOf(a)   => nested(List.fill(length)(value(a)))
    case Shape.OptionOf(a) => if chance(0.25) then None else Some(nested(value(a)))
    case Shape.EitherOf(e, a) => if chance(0.25) then Left(nested(value(e))) else Right(nested(value(a)))
    case Shape.MapOf(k, v) => nested(List.fill(length)(value(k) -> value(v)).toMap)
    case Shape.SetOf(a)    => nested(List.fill(length)(value(a)).toSet)
    case Shape.TupleOf(as) => Tuple.fromArray(as.map(value(_).asInstanceOf[Object]).toArray)
    case Shape.FnOf(as, r) => nested(Table(as.size, List.fill(length)(as.map(value) -> value(r)), default(r)))
    case Shape.Opq(o)      => value(plan.opaque(o).getOrElse(throw CannotGenerate(s"${o.name}: no definition fixes it")))
    case Shape.Data(adt)   =>
      // Deep down, a case with no fields: the value stays small.
      val cs = if depth > 2 && adt.ctors.exists(_.fields.isEmpty) then adt.ctors.filter(_.fields.isEmpty) else adt.ctors
      val c = cs(below(cs.size))
      c.singleton.getOrElse(nested(c.make(c.fields.map((_, f) => value(f)))))
    case _                 => throw CannotGenerate(Types.scala(t))
