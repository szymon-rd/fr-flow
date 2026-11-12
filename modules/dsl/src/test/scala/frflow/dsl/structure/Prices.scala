package frflow.dsl.structure

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.dsl.lifted.FrSpec
import scala.annotation.experimental

/** An item's id: a type of its own over a string. */
opaque type ItemId = String
object ItemId extends FrSpec.Opaque[ItemId, String]

/** A structure no member changes: a plain trait, no `caps.Mutable`; and a structure whose class holds it. */
@experimental object Prices:
  final case class Item(id: ItemId, net: BigInt) derives FrSpec

  /** A price list: what an item costs, and the tax in it. */
  trait Pricing:
    def price(item: Item): BigInt
    def tax: BigInt

  final class FlatPricing(val tax: BigInt) extends Pricing:
    def price(item: Item): BigInt = item.net + tax

  /** A basket: it adds up what its items cost. */
  trait Basket extends Mutable:
    update def add(item: Item): BigInt
    def due: BigInt

  final class PricedBasket(pricing: Pricing, var total: BigInt) extends Basket:
    update def add(item: Item): BigInt =
      val cost = pricing.price(item)
      total = total + cost
      total
    def due: BigInt = total
