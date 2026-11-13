package frflow.dsl.structure

import frflow.core.name.SymbolName
import frflow.dsl.vocab.{Definition, Held}

/** Holding composes: the ways down to a structure from one that holds it, itself or through what it holds. */
class HeldSuite extends munit.FunSuite:
  private def word(holder: String, part: String): (SymbolName, Definition[?]) =
    SymbolName(holder.toLowerCase) -> StructureDeclaration.held(State.typed[Any](holder), SymbolName(part.toLowerCase),
      State.typed[Any](part))
  private def held(pairs: (String, String)*): Held = Held(pairs.toList.groupMap((_, part) =>
    SymbolName(part.toLowerCase))(word(_, _)).view.mapValues(_.toMap).toMap)
  private def ways(h: Held, part: String, tops: String*): List[(String, List[String])] =
    h.ways(SymbolName(part))((holder, _) => tops.contains(holder.value)).map(w =>
      w.holder.value -> w.through.map(_.name.value))

  private val chain = held("Counter" -> "Basket", "Basket" -> "Pricing")

  test("a structure is reached from its holder by one word, and from its holder's holder by two, in order") {
    assertEquals(ways(chain, "pricing", "basket"), List("basket" -> List("basket_holds_pricing")))
    assertEquals(ways(chain, "pricing", "counter"),
      List("counter" -> List("counter_holds_basket", "basket_holds_pricing")))
  }

  test("the nearest holder accepted is where a way stops; a structure nothing accepted holds has no way") {
    assertEquals(ways(chain, "pricing", "basket", "counter"), List("basket" -> List("basket_holds_pricing")))
    assertEquals(ways(chain, "pricing", "ledger"), Nil)
    assertEquals(ways(chain, "counter", "basket"), Nil)
  }

  test("a structure two of a holder's structures hold is reached two ways") {
    val diamond = held("Shop" -> "Stock", "Shop" -> "Billing", "Stock" -> "Ledger", "Billing" -> "Ledger")
    assertEquals(ways(diamond, "ledger", "shop").map(_._2), List(
      List("shop_holds_billing", "billing_holds_ledger"), List("shop_holds_stock", "stock_holds_ledger")))
  }

  test("the word between a holder and what it holds is typed by both") {
    val (_, via) = word("Basket", "Pricing")
    assertEquals(Held.ends(via), (State.typed[Any]("Basket").ty, State.typed[Any]("Pricing").ty))
  }
