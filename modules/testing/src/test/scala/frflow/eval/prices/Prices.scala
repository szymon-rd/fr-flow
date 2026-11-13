package frflow.eval.prices

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.FrSpec
import scala.annotation.experimental

/** An item's id: a type of its own over a string. */
opaque type ItemId = String
object ItemId extends FrSpec.Opaque[ItemId, String]

/** A structure no member changes, a plain trait that is no `caps.Mutable`; a structure whose class holds it; and
  * one whose class holds that one, so what it reaches of the first is two constructors down.
  */
@experimental object Prices:
  final case class Item(id: ItemId, net: BigInt) derives FrSpec

  /** A price list: what an item costs, and the tax in it. */
  trait Pricing:
    /** What an item costs: its net price and the tax. */
    def price(item: Item): BigInt
    /** The tax added to every item's net price. */
    def tax: BigInt

  final class FlatPricing(val tax: BigInt) extends Pricing:
    def price(item: Item): BigInt = item.net + tax

  /** A basket: it adds up what its items cost. */
  trait Basket extends Mutable:
    /** Adds an item at its price: what is then due. */
    update def add(item: Item): BigInt
    /** What the items added so far cost together. */
    def due: BigInt

  final class PricedBasket(pricing: Pricing, var total: BigInt) extends Basket:
    update def add(item: Item): BigInt =
      val cost = pricing.price(item)
      total = total + cost
      total
    def due: BigInt = total

  /** A counter: it rings items up into the basket it holds. */
  trait Counter extends Mutable:
    /** Rings an item up: what the basket then has due. */
    update def ring(item: Item): BigInt
    /** How many items were rung up. */
    def count: BigInt

  final class BasketCounter(basket: Basket^, var rung: BigInt) extends Counter:
    update def ring(item: Item): BigInt =
      val due = basket.add(item)
      rung = rung + BigInt(1)
      due
    def count: BigInt = rung
