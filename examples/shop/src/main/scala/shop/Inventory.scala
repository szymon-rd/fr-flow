package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The inventory service: it reserves an order's units, and releases them when the order does not go through. */
final class Inventory(warehouse: Warehouse^):
  def reserve(o: Order): Boolean = warehouse.hold(o)
  def release(o: Order): Unit = warehouse.putBack(o)

object Inventory:
  val reserve = Declaration[(Stock, Order) -> (Boolean, Stock)]("reserving an order's units: whether they were " +
    "there, and the stock after")
  val release = Declaration[(Stock, Order) -> (Unit, Stock)]("releasing an order's units: the stock after")

  val reserveCode = updating { (inventory: Inventory^, o: Order) => inventory.reserve(o) }
  val releaseCode = updating { (inventory: Inventory^, o: Order) => inventory.release(o) }

  // The inventory's contracts: what the checkout knows of it.

  val reservedWhenAvailable = Node.claim("An order's units are reserved exactly when its product has that many " +
      "to sell.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      reserve(stock, o)._1 === (o.units <= Stock.available(stock.movements, o.sku))))

  val reservedUnitsAreTaken = Node.claim("Units reserved are no longer to sell.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      reserve(stock, o)._1 implies
        (Stock.available(reserve(stock, o)._2.movements, o.sku) ===
          Stock.available(stock.movements, o.sku) - o.units)))

  val refusedReserveChangesNothing = Node.claim("A reservation that is not made leaves the stock as it is.")(
    forall((stock: Term[Stock], o: Term[Order]) =>
      !reserve(stock, o)._1 implies (reserve(stock, o)._2 === stock)))

  val releaseUndoesReserve = Node.claim("Releasing an order's units after reserving them leaves every product " +
      "with what it had to sell.")(
    forall((stock: Term[Stock], sku: Term[String], o: Term[Order]) =>
      reserve(stock, o)._1 implies
        (Stock.available(release(reserve(stock, o)._2, o)._2.movements, sku) ===
          Stock.available(stock.movements, sku))))
