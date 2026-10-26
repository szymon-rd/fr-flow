package frflow
package lean

import frflow.fixtures.*
import frflow.protocol.ObligationName

/** The Lean of a knowledge base: terms, obligations, tries, and what a proof file may hold, on the shelf fixture. */
class GenerateSuite extends munit.FunSuite:

  private val g = Generate(shelfKb)

  test("open terms are binders; defined terms are applied to their definitions") {
    assertEquals(g.term("Item")._1, "Book")
    assertEquals(g.term("good")._1, "(Shelf.good minPages)")
    val (c, opens) = g.claim(onlyGood)
    assertEquals(c, "(Shelf.OnlyGood.claim Book (Shelf.shown picks) (Shelf.good minPages))")
    assertEquals(opens.names, List("picks", "minPages"))
    assert(g.domain.contains("abbrev Item : Type := Book"), g.domain)
    assert(g.domain.contains("def good (minPages : Int) : Book → Prop"), g.domain)
  }

  test("a node with parts is proven complete from them; a leaf has nothing to prove but that it is not contradictory") {
    val complete = g.obligation(onlyGood, ObligationName.Complete).get.statement
    assert(complete.contains("∀ (h_FromList : (Shelf.FromList.claim picks)) (h_OnlyLong") && complete.endsWith("(Shelf.OnlyGood.claim Book (Shelf.shown picks) (Shelf.good minPages))"), complete)
    assertEquals(g.obligation(pick, ObligationName.Complete), None)
    assertEquals(g.tries(onlyGood).map(_.obligation.name.lean), List("needed_FromList", "needed_OnlyLong", "needed_EveryLong", "clash", "unsat", "idle"))
    assertEquals(g.tries(fromList).map(_.obligation.name.lean), List("vacuous", "restates", "clash", "unsat"))
    assertEquals(g.tries(pick).map(_.obligation.name.lean), List("unsat"))
    // one part: whether the node says only what its part says
    assert(g.tries(fromList).find(_.obligation.name.lean == "restates").get.obligation.statement.endsWith("(h_FromList : (Shelf.FromList.claim picks)), (Shelf.Pick.claim minPages picks)"),
      g.tries(fromList).find(_.obligation.name.lean == "restates"))
    // the root with the operation doing nothing, tried at Lean's default budget; the other tries at a small one
    assert(g.idle(onlyGood).get.statement.contains("(Shelf.shown (fun (x0 : (List Book)) (x1 : Int) => []))"), g.idle(onlyGood))
    val checks = g.checks(onlyGood)
    assert(checks.contains("\n\ntheorem idle : Obl.idle") && checks.contains(s"set_option maxHeartbeats ${Generate.TryHeartbeats} in\ntheorem clash"), checks)
    assertEquals(g.trusted.map(_.id), List("Pick"))
    // the composition reaches Pick once, whatever the number of paths to it
    assertEquals(g.leaves(onlyGood).map(_.id), List("Pick"))
  }

  test("a part may only say one conjunct of its parent again: tried when the parent has as many conjuncts as parts") {
    assertEquals(LeanText.conjuncts("(((∀ x, A x) ∧ (B ∧ C)) ∧ f y z)"), List("(∀ x, A x)", "B", "C", "f y z"))
    // a binder, an arrow or a disjunction binds wider than `∧`; a string's text is not cut
    assertEquals(LeanText.conjuncts("(∀ x, A x ∧ B x)"), List("(∀ x, A x ∧ B x)"))
    assertEquals(LeanText.conjuncts("(a → b ∧ c)"), List("(a → b ∧ c)"))
    assertEquals(LeanText.conjuncts("(a ∨ b ∧ c)"), List("(a ∨ b ∧ c)"))
    assertEquals(LeanText.conjuncts("(f \"x ∧ y\")"), List("(f \"x ∧ y\")"))
    val h = Generate(handedOutKb(fromShelfAgain, hundredPages))
    assertEquals(h.tries(handedOut).map(_.obligation.name.lean), List("needed_FromShelfAgain", "needed_HundredPages",
      "restates_1_FromShelfAgain", "restates_2_FromShelfAgain", "restates_1_HundredPages", "restates_2_HundredPages", "clash", "unsat"))
    val t = h.tries(handedOut).find(_.obligation.name.lean == "restates_2_HundredPages").get
    assert(t.obligation.statement.endsWith("((HandedOut.HundredPages.claim picks) ↔ (HandedOut.HandedOut.conjunct_2 picks HandedOut.worthy))"), t.obligation.statement)
    assertEquals(t.means, "HundredPages says what conjunct 2 of HandedOut says: fold it into HandedOut, or say what HundredPages adds")
    assert(h.spec(handedOut).contains("def conjunct_2 (picks : ((List Book) → Int → (List Book))) (worthy : (Book → Prop)) : Prop"), h.spec(handedOut))
    // as many conjuncts as parts only: a third part, or a claim that is no conjunction, tries none
    assert(!Generate(handedOutKb(fromShelfAgain, hundredPages, twoHundredPages)).tries(handedOut).exists(_.obligation.name.lean.startsWith("restates")))
    assert(!g.tries(onlyGood).exists(_.obligation.name.lean.startsWith("restates")))
  }

  test("a definition with an alternative: both stay, as alternatives, and what uses the term waits for the choice") {
    val thick = Node.definition("A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Term[Book]) => b.pages >= 500))
    val kb = shelfWith(pick, thick)
    assertEquals(kb.problems, Nil)
    val undecided = Generate(kb)
    assertEquals(undecided.undecided, Set("good"))
    assertEquals(undecided.waitsForDefinition(onlyGood), List("good"))
    assertEquals(undecided.waitsForDefinition(pick), Nil)
    val chosen = Generate(kb, chosen = _ == "Thick")
    assertEquals(chosen.term("good")._1, "Shelf.good")
    assert(chosen.domain.contains("/-- Thick -/"), chosen.domain)
    // running, the first listed is used until one is chosen
    assertEquals(kb.inForce(_ => false, fallback = true).get("good").map(_.id), Some("Books"))
  }

  test("generated names are reserved") {
    val m = Param[Int => Int]("a bound")
    val clash = Node.claim("s", "w")(forall((x: Term[Int]) => m(x) >= 0))
    assert(Generate.problems(KnowledgeBase("K", "IDEA.md")(clash)).exists(_.contains("reserved")))
  }

  test("impl is proven from the promises of the operations its code calls, not those a term it reads is defined with") {
    // Again's code reads pickedFrom, defined by the shelf service's operation: it depends on PickPromise, calls nothing
    val g = Generate(readsKb)
    assertEquals(g.callees(Again.again).map(_.id), List("PickPromise"))
    assertEquals(g.calls(Again.again), Nil)
    assert(!g.obligation(Again.again, ObligationName.Impl).get.statement.contains("h_PickPromise"), g.obligation(Again.again, ObligationName.Impl))
    // code calling the operation itself is proven from its promise
    val c = Generate(callsKb)
    assertEquals(c.calls(Again.again).map(_.id), List("PickPromise"))
    assert(c.obligation(Again.again, ObligationName.Impl).get.statement.contains("h_PickPromise"), c.obligation(Again.again, ObligationName.Impl))
  }

  test("a node is witnessed by proven code, an assumption, or parts that all are; a part nothing proves witnesses nothing") {
    val unrefined = Node.claim("Some books are kept aside.", why = "A part not refined yet.")(
      forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) implies l.contains(x))).refines(onlyGood)
    val g = Generate(KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick :+ unrefined)*).implementProven(pick)(longOnes))
    assert(g.witnessed(pick) && g.witnessed(fromList))
    assert(!g.witnessed(unrefined))
    assert(!g.witnessed(onlyGood)) // one of its parts has no witness, though the others have proven code
  }
