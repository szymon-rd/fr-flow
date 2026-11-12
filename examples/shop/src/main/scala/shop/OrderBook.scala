package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The order book: the store the checkout keeps its journal in. Each method is one transaction. */
final class OrderBook(var journal: Journal) extends Mutable:
  /** Registers an order for the caller: whether it was new. Of two calls registering one order, one is told no. */
  update def register(order: String): Boolean =
    val fresh = !journal.registered.contains(order)
    if fresh then journal = journal.copy(registered = order :: journal.registered)
    fresh

  /** Records how an order ended. */
  update def settle(s: Settlement): Unit = journal = journal.copy(settled = journal.settled :+ s)

object OrderBook:
  val register = Declaration[(Journal, String) -> (Boolean, Journal)]("registering an order: whether it was new, " +
    "and the journal after")
  val settle = Declaration[(Journal, Settlement) -> (Unit, Journal)]("recording how an order ended: the journal " +
    "after")

  val registerCode = updating { (orders: OrderBook^, order: String) => orders.register(order) }
  val settleCode = updating { (orders: OrderBook^, s: Settlement) => orders.settle(s) }

  // The order book's contracts.

  val registerIsWonOnce = Node.claim("An order is registered for the caller exactly when it was not registered " +
      "before.")(
    forall((journal: Term[Journal], order: Term[String]) =>
      register(journal, order)._1 === !journal.registered.contains(order)))

  val registeredStaysRegistered = Node.claim("After registering, the order is registered, and so is every order " +
      "registered before.")(
    forall((journal: Term[Journal], order: Term[String], other: Term[String]) =>
      (other === order || journal.registered.contains(other)) implies
        register(journal, order)._2.registered.contains(other)))

  val lostRegisterChangesNothing = Node.claim("Registering an order already registered leaves the journal as it " +
      "is.")(
    forall((journal: Term[Journal], order: Term[String]) =>
      !register(journal, order)._1 implies (register(journal, order)._2 === journal)))

  val settleKeepsRegistered = Node.claim("Recording an order's end leaves the orders registered as they are.")(
    forall((journal: Term[Journal], s: Term[Settlement]) =>
      settle(journal, s)._2.registered === journal.registered))

  val settledIsRecorded = Node.claim("An order's end, once recorded, is in the journal.")(
    forall((journal: Term[Journal], s: Term[Settlement]) => settle(journal, s)._2.settled.contains(s)))
