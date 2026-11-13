package frflow.eval.agree

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import scala.annotation.experimental

/** Scala that changes state: a class whose members change its fields, and a class that holds it and a structure no
  * member changes. `AgreeSuite` runs each on the JVM and holds the code read from it, and the Rocq generated from
  * that, to the same results and the same state after.
  */
@experimental object Stateful:
  import Parcels.Parcel
  import Pure.Tariff

  /** A journal of the parcels taken: none twice, none over a weight. */
  trait Journal extends Mutable:
    update def accept(p: Parcel): Boolean
    update def clear(limit: BigInt): BigInt
    def carried: BigInt
    def holds(id: String): Boolean

  final class ListJournal(val most: BigInt, var entries: List[Parcel], var taken: BigInt) extends Journal:
    update def accept(p: Parcel): Boolean =
      val fits = !holds(p.id) && p.weight <= most
      if fits then
        entries = entries :+ p
        taken = taken + BigInt(1)
      fits
    update def clear(limit: BigInt): BigInt =
      val before = BigInt(entries.length)
      entries = entries.filter(p => p.weight <= limit)
      before - BigInt(entries.length)
    def carried: BigInt = entries.foldLeft(BigInt(0))((sum, p) => sum + p.weight)
    def holds(id: String): Boolean = entries.exists(p => p.id == id)

  /** A depot: it takes a parcel into the journal it holds, at the price of the tariff it holds. */
  trait Depot extends Mutable:
    update def take(p: Parcel): BigInt
    def income: BigInt

  final class TariffDepot(journal: Journal^, tariff: Tariff, var earned: BigInt) extends Depot:
    update def take(p: Parcel): BigInt =
      val cost = tariff.price(p)
      val taken = journal.accept(p)
      if taken then earned = earned + cost
      if taken then cost else BigInt(0)
    def income: BigInt = earned
