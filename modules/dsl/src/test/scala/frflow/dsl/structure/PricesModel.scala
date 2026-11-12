package frflow.dsl.structure

import frflow.dsl.kb.FrModel
import frflow.dsl.kb.Defining.*
import frflow.dsl.lifted.steps.StepSyntax.lifted
import frflow.dsl.node.Node
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.structure.Declaring as Declaration
import scala.annotation.experimental

/** A structure no member changes, declared as any other, and one whose class is given its word. */
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
