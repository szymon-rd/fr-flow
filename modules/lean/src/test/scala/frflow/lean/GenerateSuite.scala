package frflow
package lean

import frflow.fixtures.*
import frflow.protocol.ObligationName

/** The Lean of a FrModel: terms, obligations, tries, and what a proof file may hold, on the shelf fixture. */
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
    assert(Generate.problems(FrModel("K", "IDEA.md")(clash)).exists(_.contains("reserved")))
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

  test("a root stated of its flow is proven of its code from its parts, and rests on none of them as a callee") {
    val g = Generate(Service.kb())
    // the flow calls price, whose contract is the root's part: below it, so decided after it, not rested on
    assertEquals(g.callees(Service.sold).map(_.id), List("PricePositive"))
    assertEquals(g.reliedOn(Service.sold), Nil)
    val step = g.obligation(Service.sold, ObligationName.Complete).get.statement
    assert(step.contains("(Service.Sold.claim (Service.selling_run price))"), step)
    assertEquals(g.obligation(Service.sold, ObligationName.Impl).map(_.statement), Some(step))
  }

  test("what always holds of a type is assumed of what a statement quantifies over, and proven kept by the code") {
    val g = Generate(Invariants.shelf)
    val spec = g.spec(pick)
    assert(spec.contains("(∀ y ∈ x0, Shelf.hasPages y) → (Shelf.shelvedOnce x0) → "), spec)
    val service = Generate(Invariants.service)
    // the till's money and the item's price, both amounts: assumed of the input and of the world before
    val sold = service.spec(Service.sold)
    assert(sold.contains("(Service.notNegative x0) → (Service.notNegative x1.till) → "), sold)
    // the selling flow, the till's one writer, keeps it, given what the price's contract promises
    val kept = service.obligation(Invariants.notNegative, ObligationName.KeptBy("sell")).get.statement
    assert(kept.contains("(h_PricePositive : (Service.PricePositive.claim price))") &&
      kept.endsWith("(Service.notNegative ((Service.sold_run price) x0 x1).2.till)"), kept)
  }

  test("a node is witnessed by proven code, an assumption, or parts that all are; a part nothing proves witnesses nothing") {
    val unrefined = Node.claim("Some books are kept aside.", why = "A part not refined yet.")(
      forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) implies l.contains(x))).refines(onlyGood)
    val g = Generate(FrModel("Shelf", idea = "IDEA.md")((shelfNodes :+ pick :+ unrefined)*).implementProven(pick)(longOnes))
    assert(g.witnessed(pick) && g.witnessed(fromList))
    assert(!g.witnessed(unrefined))
    assert(!g.witnessed(onlyGood)) // one of its parts has no witness, though the others have proven code
  }

  test("a root over Declarations: each said in the code's words, at the bottom; what always holds of a store, of a world") {
    import Concepts.*
    val level = Declaration[World => BigInt]("how far the count has come, as the world stands")
    val levelAfter = Declaration[(BigInt, World) => BigInt]("how far the count has come once a request is added")
    val levelGrows: Node[?] = Node.claim("The level grows by each request's step.")(
      forall((x: Term[BigInt], now: Term[World]) => levelAfter(x, now) === level(now) + step(x)))
    val levelIsCount = Node.claim("The level is the count.")(
      forall((now: Term[World]) => level(now) === counted.in(now))).refines(levelGrows)
    val levelAfterIsCount = Node.claim("The level once a request is added is the count after adding it.")(
      forall((x: Term[BigInt], now: Term[World]) => levelAfter(x, now) === counted.in(add(x).after(now))))
      .refines(levelGrows)
    val counts = Node.claim("Adding a request adds its step to the count.")(
      forall((x: Term[BigInt], before: Term[World]) => counted.in(add(x).after(before)) === counted.in(before) + step(x)))
      .refines(levelGrows).assuming(model)
    val sized = Node.claim("A step adds one more than the request's size.")(
      forall((x: Term[BigInt]) => step(x) === when(x >= BigInt(0))(x + 1).otherwise(-x + 1))).refines(counts)
    val positive = Node.claim("The count is never negative.")(always(counted)(c => c >= BigInt(0)))
      .refines(levelGrows).assuming(writes, oneAtATime, startsAtNothing)
    val kb = FrModel("Levels")(levelGrows, levelIsCount, levelAfterIsCount, counts, sized, positive, model, writes,
      oneAtATime, startsAtNothing).implementProven(add)(adding).implementTested(step)(x => x.abs + 1)
    assertEquals(kb.problems, Nil)
    assertEquals(kb.roots.map(_.id), List("LevelGrows"))
    val g = Generate(kb)
    // a world quantified over holds what always holds of the store, as a flow's world before does
    assert(g.spec(levelIsCount).contains("(x0 : World), (Levels.positive x0.counter) → "), g.spec(levelIsCount))
    // the step: what the Declarations are says it of the proven code; the always claim is a hypothesis, not a part
    val split = g.obligation(levelGrows, ObligationName.Complete).get.statement
    assert(split.contains("(h_LevelAfterIsCount : (Levels.LevelAfterIsCount.claim levelAfter (Levels.adding_run step)))") &&
      split.contains("(h_Counts : (Levels.Counts.claim step (Levels.adding_run step)))") && !split.contains("h_Positive"), split)
    assert(g.spec(levelAfterIsCount).contains("import FrFlowGen.Levels.Domain.Def_adding_run"), g.spec(levelAfterIsCount))
    // what a Declaration is, nothing implements: not trusted of the code, and witnessed by the consistency check
    assertEquals(g.trusted.map(_.id), List("Sized"))
    assert(g.witnessed(levelGrows))
    // each found in substitution order: the step's equation, then the proven code mentioning it, then the Declarations
    val consistency = g.witnessing.file
    assert(consistency.contains("level as LevelIsCount says") && consistency.contains("levelAfter as LevelAfterIsCount says"),
      consistency)
  }
