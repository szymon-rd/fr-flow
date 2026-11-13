package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The inventory service: it reserves an order's units, and releases them when the order does not go through. */
trait Inventory extends Mutable:
  /** Reserves an order's units if its product has them to sell: whether it did. */
  update def reserve(o: Order): Boolean
  /** Releases an order's units. */
  update def release(o: Order): Unit
  /** The units of a product there are to sell. */
  def available(sku: String): BigInt

/** What the checkout knows of the inventory. */
object Inventory:
  val inventory = Declaration[Inventory]("the inventory service: it reserves and releases an order's units")

  val reservedWhenAvailable = Node.claim("An order's units are reserved exactly when its product has that many " +
      "to sell.")(
    forall((o: Term[Order]) => inventory.reserve(o).result === (o.units <= inventory.available(o.sku))))

  val reservedUnitsAreTaken = Node.claim("Units reserved are no longer to sell.")(
    forall((o: Term[Order]) =>
      inventory.reserve(o).result implies
        (inventory.available(o.sku).in(inventory.reserve(o).after) === inventory.available(o.sku) - o.units)))

  val refusedReserveChangesNothing = Node.claim("A reservation that is not made leaves every product with what " +
      "it had to sell.")(
    forall((sku: Term[String], o: Term[Order]) =>
      !inventory.reserve(o).result implies
        (inventory.available(sku).in(inventory.reserve(o).after) === inventory.available(sku))))

  val releaseUndoesReserve = Node.claim("Releasing an order's units after reserving them leaves every product " +
      "with what it had to sell.")(
    forall((sku: Term[String], o: Term[Order]) =>
      inventory.reserve(o).result implies
        (inventory.available(sku).in(inventory.release(o).in(inventory.reserve(o).after).after) ===
          inventory.available(sku))))

/** The inventory over a warehouse: a reservation is a hold, a release puts the units back. */
final class WarehouseInventory(warehouse: Warehouse^) extends Inventory:
  update def reserve(o: Order): Boolean =
    val held = warehouse.hold(o)
    held

  update def release(o: Order): Unit = warehouse.putBack(o)

  def available(sku: String): BigInt = warehouse.available(sku)
