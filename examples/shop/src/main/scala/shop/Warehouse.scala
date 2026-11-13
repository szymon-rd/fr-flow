package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The warehouse: the units of each product there are to sell. Each member that changes it is one transaction. */
trait Warehouse extends Mutable:
  /** Holds an order's units if the product has that many to sell: whether it did. */
  update def hold(o: Order): Boolean
  /** Puts an order's units back among those to sell. */
  update def putBack(o: Order): Unit
  /** The units of a product there are to sell. */
  def available(sku: String): BigInt

object Warehouse:
  val warehouse = Declaration[Warehouse]("the warehouse: the units of each product to sell")

  val holdIsMadeWhenAvailable = Node.claim("Units are held exactly when the product has that many to sell.")(
    forall((o: Term[Order]) => warehouse.hold(o).result === (o.units <= warehouse.available(o.sku))))

  val holdKeepsStocked = Node.claim("Holding units if the product has them leaves a product that is not " +
      "oversold not oversold.")(
    forall((sku: Term[String], o: Term[Order]) =>
      (warehouse.available(sku) >= 0) implies (warehouse.available(sku).in(warehouse.hold(o).after) >= 0)))

  val heldUnitsAreTaken = Node.claim("Units held are no longer to sell; every other product has what it had.")(
    forall((sku: Term[String], o: Term[Order]) =>
      warehouse.hold(o).result implies
        (warehouse.available(sku).in(warehouse.hold(o).after) ===
          warehouse.available(sku) - when(sku === o.sku)(o.units).otherwise(0))))

  val refusedHoldChangesNothing = Node.claim("A hold that is not made leaves the warehouse as it is.")(
    forall((o: Term[Order]) => !warehouse.hold(o).result implies (warehouse.hold(o).after === warehouse.current)))

  val putBackKeepsStocked = Node.claim("Putting units back leaves a product that is not oversold not oversold.")(
    forall((sku: Term[String], o: Term[Order]) =>
      (warehouse.available(sku) >= 0) implies (warehouse.available(sku).in(warehouse.putBack(o).after) >= 0)))

  val unitsPutBackAreToSell = Node.claim("Units put back are to sell again; every other product has what it had.")(
    forall((sku: Term[String], o: Term[Order]) =>
      warehouse.available(sku).in(warehouse.putBack(o).after) ===
        warehouse.available(sku) + when(sku === o.sku)(o.units).otherwise(0)))

/** The warehouse kept as every movement of its stock, oldest first: what a product has to sell is the sum of its
  * movements.
  */
final class MovementWarehouse(var movements: List[Movement]) extends Warehouse:
  update def hold(o: Order): Boolean =
    val has = o.units <= available(o.sku)
    if has then movements = movements :+ Movement(o.id, o.sku, -o.units)
    has

  update def putBack(o: Order): Unit = movements = movements :+ Movement(o.id, o.sku, o.units)

  def available(sku: String): BigInt =
    movements.filter(m => m.sku == sku).foldLeft(BigInt(0))((sum, m) => sum + m.units)
