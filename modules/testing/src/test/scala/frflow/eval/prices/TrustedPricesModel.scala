package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** A basket over a price list that has no class here: one from elsewhere (a library's, a remote service), known
  * to the model only by what is assumed of it (`pricing.provided`). The model is valid; Rocq does not build it
  * yet: a structure with no class has no type in the Rocq model.
  */
@experimental object TrustedPricesModel:
  import Prices.{Basket, Item, PricedBasket, Pricing}

  val pricing = Declaration[Pricing]("a price list from elsewhere: what each item costs")
  val basket = Declaration[Basket]("the basket: it adds up what its items cost")

  val priceCoversNet = Node.assumption("The price list never prices an item under its net price.")(
    forall((i: Term[Item]) => pricing.price(i) >= i.net))

  val addingRaisesDueByNet = Node.claim("Adding an item raises what is due by its net price at least.")(
    forall((i: Term[Item]) => basket.due.in(basket.add(i).after) >= basket.due + i.net))

  val model: FrModel = FrModel("TrustedPrices")(addingRaisesDueByNet,
    priceCoversNet.refines(addingRaisesDueByNet), pricing.provided, basket.define(lifted[PricedBasket](pricing)))
