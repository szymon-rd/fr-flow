package shop

import frflow.*

// The shop's data: what its stores keep and its services speak in.

/** One side of a payment: an account's balance changed by an amount (negative: taken), for an order. */
final case class Posting(order: String, account: String, amount: BigInt) derives FrSpec

/** Units of a product entering what the warehouse has to sell (a delivery, a hold put back) or leaving it
  * (negative: held for an order).
  */
final case class Movement(order: String, sku: String, units: BigInt) derives FrSpec

/** How an order ended. */
enum Status derives FrSpec:
  case Confirmed, Rejected

/** An order's end, as the order book records it. */
final case class Settlement(order: String, status: Status) derives FrSpec

/** An order: units of one product for a customer, for an amount, under the id its sender gave it. A sender that
  * hears nothing sends the order again under the same id.
  */
final case class Order(id: String, customer: String, sku: String, units: BigInt, amount: BigInt)

object Order:
  /** At least one unit, for a positive amount: the API refuses any other before a service sees it. */
  given FrSpec[Order] = FrSpec.derived[Order].where(o => o.units > 0 && o.amount > 0)

/** What a charge is answered: done, refused (the customer cannot cover it), or a duplicate of one claimed. */
enum Charged derives FrSpec:
  case Done, Refused, Duplicate

/** What placing an order is answered. */
enum Placement derives FrSpec:
  case Confirmed, OutOfStock, PaymentRefused, Duplicate
