package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** A counter over the basket over the price list: three structures, each class given the word of the one it holds.
  * The counter's claims reach the price list, which its constructor is not given: the basket's is. Each is proven
  * from the claims on the basket, which are its parts.
  */
@experimental object CounterModel:
  import Prices.{BasketCounter, Counter, FlatPricing, Item, PricedBasket}
  import PricesModel.{addingAddsThePrice, addingGivesWhatIsDue, basket, priceIsNetAndTax, pricing}

  val counter = Declaration[Counter]("the counter: it rings items up into the basket it holds")

  val ringingAddsThePrice = Node.claim("Ringing an item up adds its price to what the counter's basket has due.")(
    forall((i: Term[Item]) => basket.due.in(counter.ring(i).after) === basket.due + pricing.price(i)))

  val ringingKeepsThePriceList = Node.claim("Ringing an item up leaves the price list as it was: the one of the " +
      "basket the counter holds.")(
    forall((i: Term[Item]) => pricing.price(i).in(counter.ring(i).after) === pricing.price(i)))

  val ringingCounts = Node.claim("Ringing an item up counts it, and gives what the basket then has due.")(
    forall((i: Term[Item]) => (counter.count.in(counter.ring(i).after) === counter.count + 1) &&
      (counter.ring(i).result === basket.due.in(basket.in(counter.ring(i).after)))))

  val model: FrModel = FrModel("Ringing")(priceIsNetAndTax, addingGivesWhatIsDue.refines(ringingCounts),
    addingAddsThePrice.refines(ringingAddsThePrice, ringingKeepsThePriceList), ringingAddsThePrice,
    ringingKeepsThePriceList, ringingCounts, pricing.define(lifted[FlatPricing]),
    basket.define(lifted[PricedBasket](pricing)), counter.define(lifted[BasketCounter](basket)))
