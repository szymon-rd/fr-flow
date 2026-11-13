package frflow.eval.agree

import scala.annotation.experimental

/** Scala that changes nothing, a member for each kind of construct the compiler reads (`docs/LIFTED.md`, "What the
  * compiler reads"): numbers and truth values, records and enums, options, lists, maps and sets, pairs. `AgreeSuite`
  * runs each on the JVM and holds the code read from it, and the Rocq generated from that, to the same results.
  */
@experimental object Pure:
  import Parcels.{Parcel, Zone}

  /** Numbers and truth values: arithmetic, comparisons, `if`, a `val`, an `inline def`, a method of the class. */
  trait Arith:
    def blend(a: BigInt, b: BigInt): BigInt
    def ordered(a: BigInt, b: BigInt, c: BigInt): Boolean

  final class PlainArith(val bias: BigInt) extends Arith:
    inline def twice(x: BigInt): BigInt = x + x
    def clamp(x: BigInt, lo: BigInt, hi: BigInt): BigInt = if x < lo then lo else if x > hi then hi else x
    def blend(a: BigInt, b: BigInt): BigInt =
      val d = a - b
      val distance = if d >= BigInt(0) then d else -d
      twice(distance) + clamp(a, BigInt(0), bias) - BigInt(3)
    def ordered(a: BigInt, b: BigInt, c: BigInt): Boolean =
      (a < b && b <= c) || (a > b && b >= c) || !(a != bias) || a == c

  /** Records and enums: a field, a record made, a copy, a match on an enum's cases, equality of data. */
  trait Tariff:
    def price(p: Parcel): BigInt
    def reroute(p: Parcel, km: BigInt): Parcel
    def same(p: Parcel, q: Parcel): Boolean
    def flagged(p: Parcel, limit: BigInt): Parcel

  final class ZoneTariff(val base: BigInt) extends Tariff:
    def price(p: Parcel): BigInt =
      val byZone = p.zone match
        case Zone.Local        => base
        case Zone.Regional(km) => base + km
        case a: Zone.Abroad    => if a.country == "far" then base + a.km + a.km else base + a.km
      if p.express then byZone + p.weight else byZone
    def reroute(p: Parcel, km: BigInt): Parcel =
      if km <= BigInt(0) then p.copy(zone = Zone.Local)
      else if km < BigInt(50) then p.copy(zone = Zone.Regional(km), express = false)
      else Parcel(p.id, p.weight, Zone.Abroad("far", km), p.express)
    def same(p: Parcel, q: Parcel): Boolean = p == q || (p.id == q.id && p.zone != q.zone)
    def flagged(p: Parcel, limit: BigInt): Parcel = p.copy(express = p.weight > limit || p.express)

  /** Options: made, matched, and each operation read. */
  trait Maybe:
    def total(a: Option[BigInt], b: Option[BigInt]): BigInt
    def pick(a: Option[BigInt], limit: BigInt): Option[BigInt]
    def checks(a: Option[BigInt], limit: BigInt): Boolean

  final class PlainMaybe(val default: BigInt) extends Maybe:
    def total(a: Option[BigInt], b: Option[BigInt]): BigInt =
      val left = a match
        case Some(x) => x
        case None    => default
      left + b.getOrElse(default) + b.fold(BigInt(0))(x => x + x)
    def pick(a: Option[BigInt], limit: BigInt): Option[BigInt] =
      if a.isEmpty then Some(limit) else if a.exists(x => x > limit) then None else a.map(x => x + default)
    def checks(a: Option[BigInt], limit: BigInt): Boolean =
      (a.isDefined && a.forall(x => x <= limit)) || a.contains(default) || (a.isEmpty && limit < default)

  /** Lists: made, taken apart by their operations, folded. */
  trait Lists:
    def heavy(ps: List[Parcel], limit: BigInt): List[Parcel]
    def load(ps: List[Parcel]): BigInt
    def first(ps: List[Parcel], limit: BigInt): Option[Parcel]
    def shape(xs: List[BigInt], x: BigInt): List[BigInt]
    def facts(xs: List[BigInt], x: BigInt): Boolean

  final class PlainLists(val step: BigInt) extends Lists:
    def heavy(ps: List[Parcel], limit: BigInt): List[Parcel] = ps.filter(p => p.weight > limit)
    def load(ps: List[Parcel]): BigInt = ps.map(p => p.weight).foldLeft(BigInt(0))((sum, w) => sum + w)
    def first(ps: List[Parcel], limit: BigInt): Option[Parcel] = ps.find(p => p.express && p.weight <= limit)
    def shape(xs: List[BigInt], x: BigInt): List[BigInt] =
      val grown = (x :: xs) ++ List(step, x) :+ BigInt(xs.length)
      if xs.isEmpty then Nil else grown.flatMap(y => List(y, y + step))
    def facts(xs: List[BigInt], x: BigInt): Boolean =
      (xs.nonEmpty && xs.forall(y => y >= x)) || xs.exists(y => y == x + step) || xs.contains(step)

  /** Maps and sets, read at a key or a member, and pairs. */
  trait Tables:
    def stock(m: Map[String, BigInt], k: String): BigInt
    def restocked(m: Map[String, BigInt], k: String, n: BigInt): Option[BigInt]
    def tagged(s: Set[String], u: Set[String], t: String): Boolean
    def swap(p: (BigInt, String)): (String, BigInt)

  final class PlainTables(val floor: BigInt) extends Tables:
    def stock(m: Map[String, BigInt], k: String): BigInt =
      if m.contains(k) then m.getOrElse(k, floor) + floor else floor
    def restocked(m: Map[String, BigInt], k: String, n: BigInt): Option[BigInt] =
      m.updated(k, m.getOrElse(k, floor) + n).get(if n > floor then k else "tea")
    def tagged(s: Set[String], u: Set[String], t: String): Boolean =
      (s + "new").contains(t) && !(s ++ u).contains("far")
    def swap(p: (BigInt, String)): (String, BigInt) = (p._2, p._1 + floor)
