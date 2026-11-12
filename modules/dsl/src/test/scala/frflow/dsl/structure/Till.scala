package frflow.dsl.structure

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.dsl.lifted.FrSpec
import scala.annotation.experimental

/** A sale's id: a type of its own over a string. */
opaque type SaleId = String
object SaleId extends FrSpec.Opaque[SaleId, String]

/** A structure as a trait, and a class that implements it: what `Definition[Till]` and `lifted(CashTill(…))` read. */
@experimental object Till:
  final case class Sale(id: SaleId, amount: BigInt) derives FrSpec

  /** A till: it takes a sale once, and says what it holds. */
  trait Till extends Mutable:
    update def take(s: Sale): Boolean
    def taken(id: SaleId): Boolean
    def total: BigInt
    /** How many sales it took: a member no claim mentions. */
    def count: BigInt

  final class CashTill(var sales: List[Sale]) extends Till:
    update def take(s: Sale): Boolean =
      val fresh = !taken(s.id)
      if fresh then sales = sales :+ s
      fresh
    def taken(id: SaleId): Boolean = sales.exists(x => x.id == id)
    def total: BigInt = sales.foldLeft(BigInt(0))((sum, x) => sum + x.amount)
    def count: BigInt = BigInt(sales.size)
