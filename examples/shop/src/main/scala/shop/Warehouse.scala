package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The warehouse: the store the inventory service keeps the stock in. Each method is one transaction. */
final class Warehouse(var stock: Stock) extends Mutable:
  /** Holds an order's units if the product has that many to sell: whether it did. */
  update def hold(o: Order): Boolean =
    val has = o.units <= Stock.available(stock.movements, o.sku)
    if has then stock = stock.copy(movements = stock.movements :+ Movement(o.id, o.sku, -o.units))
    has

  /** Puts an order's units back among those to sell. */
  update def putBack(o: Order): Unit =
    stock = stock.copy(movements = stock.movements :+ Movement(o.id, o.sku, o.units))

object Warehouse:
  val hold = Definition[(Stock, Order) -> (Boolean, Stock)]("holding an order's units if its product has them " +
    "to sell: whether it did, and the stock after")
  val putBack = Definition[(Stock, Order) -> (Unit, Stock)]("putting an order's units back among those to sell: " +
    "the stock after")

  val holdCode = updating { (warehouse: Warehouse^, o: Order) => warehouse.hold(o) }
  val putBackCode = updating { (warehouse: Warehouse^, o: Order) => warehouse.putBack(o) }

  // The warehouse's contracts.

  val holdIsMadeWhenAvailable = Node.claim("Units are held exactly when the product has that many to sell.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      hold(stock, o)._1 === (o.units <= Stock.available(stock.movements, o.sku))))

  val holdKeepsStocked = Node.claim("Holding units if the product has them leaves no product oversold.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      Stock.stocked(stock) implies Stock.stocked(hold(stock, o)._2)))

  val heldUnitsAreTaken = Node.claim("Units held are no longer to sell; every other product has what it had.")(
    forall((stock: Term[Stock], sku: Term[String], o: Term[Order]) =>
      hold(stock, o)._1 implies
        (Stock.available(hold(stock, o)._2.movements, sku) ===
          Stock.available(stock.movements, sku) - when(sku === o.sku)(o.units).otherwise(0))))

  val refusedHoldChangesNothing = Node.claim("A hold that is not made leaves the stock as it is.")(
    forall((stock: Term[Stock], o: Term[Order]) => !hold(stock, o)._1 implies (hold(stock, o)._2 === stock)))

  val putBackKeepsStocked = Node.claim("Putting units back leaves no product oversold.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      Stock.stocked(stock) implies Stock.stocked(putBack(stock, o)._2)))

  val unitsPutBackAreToSell = Node.claim("Units put back are to sell again; every other product has what it had.")(
    forall((stock: Term[Stock], sku: Term[String], o: Term[Order]) =>
      Stock.available(putBack(stock, o)._2.movements, sku) ===
        Stock.available(stock.movements, sku) + when(sku === o.sku)(o.units).otherwise(0)))
