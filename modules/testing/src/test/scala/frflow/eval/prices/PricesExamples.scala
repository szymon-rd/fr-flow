package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** The basket at work over a price list with a tax of 2: a state is an object of the class (`holding`). */
@experimental class PricesExamples extends FrFlowExamples(PricesModel.model):
  import Prices.{FlatPricing, Item, PricedBasket}
  import PricesModel.{basket, pricing}

  private val list = pricing.holding(FlatPricing(BigInt(2)))
  private val empty = basket.holding(PricedBasket(FlatPricing(BigInt(2)), BigInt(0)))
  private val pen = Item("pen", 5)

  example("an item costs its net price and the tax"):
    pricing.price(pen).in(list) is BigInt(7)

  example("an item added is due at its price"):
    val added = basket.add(pen).in(empty)
    (added.result is BigInt(7)) && (basket.due.in(added.after) is BigInt(7))
