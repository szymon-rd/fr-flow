package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import Warehouse.warehouse

/** The inventory service: it reserves an order's units, and releases them when the order does not go through. */
trait Inventory extends Mutable:
  /** Reserves an order's units if its product has them to sell: whether it did. */
  update def reserve(o: Order): Boolean
  /** Releases an order's units. */
  update def release(o: Order): Unit

/** What the checkout knows of the inventory, said of the warehouse the inventory holds. */
object Inventory:
  val inventory = Declaration[Inventory]("the inventory service: it reserves and releases an order's units")

  val reservedWhenAvailable = Node.claim("An order's units are reserved exactly when its product has that many " +
      "to sell.")(
    forall((o: Term[Order]) => inventory.reserve(o).result === (o.units <= warehouse.available(o.sku))))

  val reservedUnitsAreTaken = Node.claim("Units reserved are no longer to sell.")(
    forall((o: Term[Order]) =>
      inventory.reserve(o).result implies
        (warehouse.available(o.sku).in(inventory.reserve(o).after) === warehouse.available(o.sku) - o.units)))

  val refusedReserveChangesNothing = Node.claim("A reservation that is not made leaves every product with what " +
      "it had to sell.")(
    forall((sku: Term[String], o: Term[Order]) =>
      !inventory.reserve(o).result implies
        (warehouse.available(sku).in(inventory.reserve(o).after) === warehouse.available(sku))))

  val releaseUndoesReserve = Node.claim("Releasing an order's units after reserving them leaves every product " +
      "with what it had to sell.")(
    forall((sku: Term[String], o: Term[Order]) =>
      inventory.reserve(o).result implies
        (warehouse.available(sku).in(inventory.release(o).in(inventory.reserve(o).after).after) ===
          warehouse.available(sku))))

  val reserveKeepsStocked = Node.claim("Reserving an order's units leaves a product that is not oversold not " +
      "oversold.")(
    forall((sku: Term[String], o: Term[Order]) =>
      (warehouse.available(sku) >= 0) implies (warehouse.available(sku).in(inventory.reserve(o).after) >= 0)))

  val releaseKeepsStocked = Node.claim("Releasing an order's units leaves a product that is not oversold not " +
      "oversold.")(
    forall((sku: Term[String], o: Term[Order]) =>
      (warehouse.available(sku) >= 0) implies (warehouse.available(sku).in(inventory.release(o).after) >= 0)))

/** The inventory over a warehouse: a reservation is a hold, a release puts the units back. */
final class WarehouseInventory(warehouse: Warehouse^) extends Inventory:
  update def reserve(o: Order): Boolean =
    val held = warehouse.hold(o)
    held

  update def release(o: Order): Unit = warehouse.putBack(o)
