package frflow
package testing

import frflow.types.Shape
import scala.collection.mutable

/** What a contract's cases are made of: the generators given for some types, the examples' values (seeds, by type),
  * their numbers, and the types the definitions in force give the opaque terms. For an outside system's code (an
  * assumption's: a database), a given generator says what the outside can hold, and is all that type is drawn from,
  * with the examples' values: data it cannot hold (two rows with one key) is no finding.
  */
private[frflow] final class Plan(custom: Map[String, Gen[?]], seeds: Map[String, Vector[Any]], val numbers: List[BigInt],
    opaques: Map[String, LeanType[?]], outside: Boolean = false):
  private val keys = new java.util.IdentityHashMap[LeanType[?], String]()
  /** A type's name, as Scala tells its values apart (an Int is not a Long, though Lean names both `Int`). */
  def key(t: LeanType[?]): String =
    Option(keys.get(t)).getOrElse { val k = Plan.name(t); keys.put(t, k); k }
  def customFor(t: LeanType[?]): Option[Gen[?]] = custom.get(key(t))
  /** Only the given generator and the examples make this type's values. */
  def only(t: LeanType[?]): Boolean = outside && custom.contains(key(t))
  /** The type holds, at some depth, values only a given generator makes: a value near one of its seeds (a list's
    * element repeated, a field changed) may be one the outside cannot hold, so none is made.
    */
  def holdsOnly(t: LeanType[?]): Boolean =
    def go(u: LeanType[?], seen: Set[String]): Boolean =
      val k = key(u)
      only(u) || !seen(k) && (u.shape match
        case Shape.ListOf(a)   => go(a, seen + k)
        case Shape.OptionOf(a) => go(a, seen + k)
        case Shape.EitherOf(e, a) => go(e, seen + k) || go(a, seen + k)
        case Shape.SetOf(a)    => go(a, seen + k)
        case Shape.MapOf(x, y) => go(x, seen + k) || go(y, seen + k)
        case Shape.TupleOf(as) => as.exists(go(_, seen + k))
        case Shape.FnOf(as, r) => (as :+ r).exists(go(_, seen + k))
        case Shape.Data(adt)   => adt.ctors.exists(_.fields.exists((_, f) => go(f, seen + k)))
        case Shape.Opq(o)      => opaques.get(o.name).exists(go(_, seen + k))
        case _                 => false)
    outside && custom.nonEmpty && go(t, Set.empty)
  def seedsOf(t: LeanType[?]): Vector[Any] = seeds.getOrElse(key(t), Vector.empty)
  def opaque(o: Opaque): Option[LeanType[?]] = opaques.get(o.name)

private[frflow] object Plan:
  def name(t: LeanType[?]): String = t.shape match
    case Shape.Num(k)      => k.toString
    case Shape.Data(a)     => a.name
    case Shape.Opq(o)      => s"${o.name}.T"
    case Shape.ListOf(a)   => s"List[${name(a)}]"
    case Shape.OptionOf(a) => s"Option[${name(a)}]"
    case Shape.EitherOf(e, a) => s"Either[${name(e)}, ${name(a)}]"
    case Shape.SetOf(a)    => s"Set[${name(a)}]"
    case Shape.MapOf(k, v) => s"Map[${name(k)}, ${name(v)}]"
    case Shape.TupleOf(as) => as.map(name).mkString("(", ", ", ")")
    case Shape.FnOf(as, r) => (as :+ r).map(name).mkString("(", " => ", ")")
    case other             => other.toString

  /** The values a value holds, by type: a grant table gives grants, users and paths. */
  def harvest(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], key: LeanType[?] => String,
      into: mutable.Map[String, Vector[Any]]): Unit =
    def add(x: Any) = into.updateWith(key(t))(s => Some(s.fold(Vector(x))(xs => if xs.contains(x) || xs.size >= 12 then xs else xs :+ x)))
    def go(u: LeanType[?], x: Any) = harvest(u, x, opaques, key, into)
    (t.shape, v) match
      case (Shape.ListOf(a), xs: List[?])     => add(v); xs.foreach(go(a, _))
      case (Shape.OptionOf(a), Some(x))       => add(v); go(a, x)
      case (Shape.EitherOf(e, _), Left(x))    => add(v); go(e, x)
      case (Shape.EitherOf(_, a), Right(x))   => add(v); go(a, x)
      case (Shape.SetOf(a), xs: Set[?])       => add(v); xs.foreach(go(a, _))
      case (Shape.MapOf(k, w), m: Map[?, ?])  => add(v); m.foreach((x, y) => { go(k, x); go(w, y) })
      case (Shape.TupleOf(as), p: Product)    => add(v); as.zip(p.productIterator.toList).foreach(go(_, _))
      case (Shape.Data(adt), p)               => add(v); adt.ctorOf(p).fields.zip(fields(p)).foreach { case ((_, f), x) => go(f, x) }
      case (Shape.Opq(o), x)                  => add(v); opaques.get(o.name).foreach(go(_, x))
      case (Shape.FnOf(as, r), t: Table)      => add(v); t.entries.foreach((ks, x) => { as.zip(ks).foreach(go(_, _)); go(r, x) })
      case (Shape.FnOf(_, _), _) | (Shape.Unknown, _) => ()
      case _                                  => add(v)
  private def fields(v: Any): List[Any] = v match
    case p: Product => p.productIterator.toList
    case _          => Nil
