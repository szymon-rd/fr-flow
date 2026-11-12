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

  val addingAddsThePrice = Node.claim("An item added adds to what is due.")(
    forall((i: Term[Item]) => basket.due.in(basket.add(i).after) === basket.add(i).result))

  val model: FrModel = FrModel("Prices")(priceIsNetAndTax, addingAddsThePrice,
    pricing.define(lifted[FlatPricing]), basket.define(lifted[PricedBasket](pricing)))
