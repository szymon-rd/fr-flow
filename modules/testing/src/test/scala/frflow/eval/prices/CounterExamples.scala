package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** The counter at work over a price list with a tax of 2, reached through the basket it holds. */
@experimental class CounterExamples extends FrFlowExamples(CounterModel.model):
  import CounterModel.counter
  import Prices.{BasketCounter, FlatPricing, Item, PricedBasket}
  import PricesModel.{basket, pricing}

  private val start = counter.holding(BasketCounter(PricedBasket(FlatPricing(BigInt(2)), BigInt(0)), BigInt(0)))
  private val pen = Item(ItemId("pen"), 5)

  example("an item rung up is due at its price, by the price list two constructors down"):
    val rung = counter.ring(pen).in(start)
    (rung.result is BigInt(7)) && (pricing.price(pen).in(rung.after) is BigInt(7))

  example("the price list is reached one holder at a time as it is at once"):
    val after = counter.ring(pen).in(start).after
    (pricing.tax.in(basket.in(after)) is BigInt(2)) && (pricing.tax.in(pricing.in(basket.in(after))) is BigInt(2))
