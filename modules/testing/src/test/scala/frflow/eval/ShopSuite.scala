package frflow.eval

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import frflow.testing.{Agreement, Settings}
import frflow.testing.Agreement.Outcome as Agreed
import frflow.testing.report.Seed
import scala.annotation.experimental
import shop.{Books, Checkout, Forgetful, Inventory, Journal, Ledger, Movement, Order, OrderBook, Payments}
import shop.{Placement, Posting, ShopExamples, Stock, Warehouse, undisturbed}

/** The shop (`examples/shop`): its model is valid, and each of its lifted functions' Scala (a service's method run
  * on stores made from the state, a store's transaction, a function of the data) agrees with the term read from it.
  */
@experimental class ShopSuite extends munit.FunSuite:
  private val elaborated = shop.shop.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
  private val settings = Settings(300, Seed(1))

  test("the shop's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("each lifted function's Scala agrees with the term read from it, on generated cases") {
    val reports = Agreement.of(elaborated, settings)(Books.balance, Books.made, Books.solvent, Books.orderly,
      Stock.available, Stock.stocked, Journal.confirmed, undisturbed, Checkout.others, Ledger.claimCode,
      Ledger.chargeIfCoveredCode, Warehouse.holdCode, Warehouse.putBackCode, OrderBook.registerCode,
      OrderBook.settleCode, Inventory.reserveCode, Inventory.releaseCode, Payments.chargeCode, Checkout.placeCode,
      Forgetful.forgetfulCode)
    assertEquals(reports.filterNot(_.agrees).map(r => r.code.value -> r.outcome), Nil)
    assertEquals(reports.map(_.outcome).distinct, List(Agreed.Agree(300)))
  }

  test("its examples hold of its code: the race for the last unit among them") {
    val examples = ShopExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 7)
  }

  test("the services as production calls them: stores changed by one call after another") {
    val warehouse = Warehouse(Stock(List(Movement("delivery", "tea", 1))))
    val ledger = Ledger(Books(List(Posting("top-up", "ann", 50), Posting("top-up", "bob", 50)), List("top-up")))
    val checkout = Checkout(Inventory(warehouse), Payments(ledger), OrderBook(Journal(Nil, Nil)))
    assertEquals(checkout.place(Order("o3", "ann", "tea", 1, 80)), Placement.PaymentRefused)
    assertEquals(checkout.place(Order("o1", "ann", "tea", 1, 30)), Placement.Confirmed)
    assertEquals(checkout.place(Order("o1", "ann", "tea", 1, 30)), Placement.Duplicate)
    assertEquals(checkout.place(Order("o2", "bob", "tea", 1, 30)), Placement.OutOfStock)
    assertEquals((Books.balance(ledger.books.postings, "ann"), Books.balance(ledger.books.postings, "shop")),
      (BigInt(20), BigInt(30)))
    assert(Stock.stocked(warehouse.stock) && Books.solvent(ledger.books) && Books.orderly(ledger.books))
  }
