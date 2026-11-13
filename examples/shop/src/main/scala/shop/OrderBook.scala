package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The order book: the orders registered, and how each ended. Each member that changes it is one transaction. */
trait OrderBook extends Mutable:
  /** Registers an order for the caller: whether it was new. Of two calls registering one order, one is told no. */
  update def register(order: String): Boolean
  /** Records how an order ended. */
  update def settle(s: Settlement): Unit
  /** Whether an order was registered. */
  def registered(order: String): Boolean
  /** Whether an order is recorded as confirmed. */
  def confirmed(order: String): Boolean

object OrderBook:
  val orders = Declaration[OrderBook]("the order book: the orders registered, and how each ended")

  val registerIsWonOnce = Node.claim("An order is registered for the caller exactly when it was not registered " +
      "before.")(
    forall((order: Term[String]) => orders.register(order).result === !orders.registered(order)))

  val registeredStaysRegistered = Node.claim("After registering, the order is registered, and so is every order " +
      "registered before.")(
    forall((order: Term[String], other: Term[String]) =>
      (other === order || orders.registered(other)) implies
        orders.registered(other).in(orders.register(order).after)))

  val lostRegisterChangesNothing = Node.claim("Registering an order already registered leaves the order book as " +
      "it is.")(
    forall((order: Term[String]) =>
      !orders.register(order).result implies (orders.register(order).after === orders.current)))

  val settleKeepsRegistered = Node.claim("Recording an order's end leaves the orders registered as they are.")(
    forall((order: Term[String], s: Term[Settlement]) =>
      orders.registered(order).in(orders.settle(s).after) === orders.registered(order)))

  val settledIsRecorded = Node.claim("An order recorded as confirmed is confirmed in the order book.")(
    forall((s: Term[Settlement]) =>
      (s.status === Status.Confirmed) implies orders.confirmed(s.order).in(orders.settle(s).after)))

/** The order book kept as the orders registered, newest first, and how each ended, oldest first. */
final class JournalOrderBook(var registrations: List[String], var settled: List[Settlement]) extends OrderBook:
  update def register(order: String): Boolean =
    val fresh = !registered(order)
    if fresh then registrations = order :: registrations
    fresh

  update def settle(s: Settlement): Unit = settled = settled :+ s

  def registered(order: String): Boolean = registrations.contains(order)
  def confirmed(order: String): Boolean = settled.exists(s => s.order == order && s.status == Status.Confirmed)
