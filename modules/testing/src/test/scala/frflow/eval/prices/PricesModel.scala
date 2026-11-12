package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** The price list and the basket as structures: each a Declaration of its trait, defined by its class. */
@experimental object PricesModel:
  import Prices.{Basket, FlatPricing, Item, PricedBasket, Pricing}

  val pricing = Declaration[Pricing]("the price list: what each item costs")
  val basket = Declaration[Basket]("the basket: it adds up what its items cost")

  val priceIsNetAndTax = Node.claim("An item costs its net price and the tax.")(
    forall((i: Term[Item]) => pricing.price(i) === i.net + pricing.tax))

  val addingGivesWhatIsDue = Node.claim("Adding an item gives what is then due.")(
    forall((i: Term[Item]) => basket.due.in(basket.add(i).after) === basket.add(i).result))

  val addingAddsThePrice = Node.claim("Adding an item adds its price, by the price list the basket holds, to " +
      "what is due, and leaves that price list as it was.")(
    forall((i: Term[Item]) =>
      (basket.due.in(basket.add(i).after) === basket.due + pricing.price(i)) &&
        (pricing.price(i).in(basket.add(i).after) === pricing.price(i))))

  val model: FrModel = FrModel("Prices")(priceIsNetAndTax, addingGivesWhatIsDue, addingAddsThePrice,
    pricing.define(lifted[FlatPricing]), basket.define(lifted[PricedBasket](pricing)))
