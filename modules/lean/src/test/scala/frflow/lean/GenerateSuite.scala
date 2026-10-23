package frflow
package lean

import frflow.fixtures.*

/** The Lean of a knowledge base: terms, obligations, tries, and what a proof file may hold, on the shelf fixture. */
class GenerateSuite extends munit.FunSuite:

  private val g = Generate(shelfKb)

  test("a node with several parents is a part of each; a parent's parts are the nodes under it") {
    assertEquals(shelfKb.parentsOf(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(shelfKb.parts(onlyGood).map(_.id), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(shelfKb.parts(fromList).map(_.id), List("Pick"))
    assertEquals(shelfKb.ancestors(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong", "OnlyGood"))
    // the composition reaches Pick once, whatever the number of paths to it
    assertEquals(g.leaves(onlyGood).map(_.id), List("Pick"))
  }

  test("open terms are binders; defined terms are applied to their definitions") {
    assertEquals(g.term("Item")._1, "Book")
    assertEquals(g.term("good")._1, "(Shelf.good minPages)")
    val (c, opens) = g.claim(onlyGood)
    assertEquals(c, "(Shelf.OnlyGood.claim Book (Shelf.shown picks) (Shelf.good minPages))")
    assertEquals(opens.names, List("picks", "minPages"))
    assert(g.domain.contains("abbrev Item : Type := Book"), g.domain)
    assert(g.domain.contains("def good (minPages : Int) : Book → Prop"), g.domain)
    // the definitions a node uses, however nested
    assertEquals(shelfKb.definitionsUsed(onlyGood, g.inForce).map(_.id).sorted, List("Books", "Picking"))
    assertEquals(shelfKb.definitionsUsed(pick, g.inForce), Nil)
  }

  test("a node with parts is proven complete from them; a leaf has nothing to prove but that it is not contradictory") {
    val complete = g.obligation(onlyGood, "complete").get.statement
    assert(complete.contains("∀ (h_FromList : (Shelf.FromList.claim picks)) (h_OnlyLong") && complete.endsWith("(Shelf.OnlyGood.claim Book (Shelf.shown picks) (Shelf.good minPages))"), complete)
    assertEquals(g.obligation(pick, "complete"), None)
    assertEquals(g.tries(onlyGood).map(_.obligation.name), List("needed_FromList", "needed_OnlyLong", "needed_EveryLong", "clash", "unsat", "idle"))
    assertEquals(g.tries(fromList).map(_.obligation.name), List("vacuous", "restates", "clash", "unsat"))
    assertEquals(g.tries(pick).map(_.obligation.name), List("unsat"))
    // one part: whether the node says only what its part says
    assert(g.tries(fromList).find(_.obligation.name == "restates").get.obligation.statement.endsWith("(h_FromList : (Shelf.FromList.claim picks)), (Shelf.Pick.claim minPages picks)"),
      g.tries(fromList).find(_.obligation.name == "restates"))
    // the root with the operation doing nothing, tried at Lean's default budget; the other tries at a small one
    assert(g.idle(onlyGood).get.statement.contains("(Shelf.shown (fun (x0 : (List Book)) (x1 : Int) => []))"), g.idle(onlyGood))
    val checks = g.checks(onlyGood)
    assert(checks.contains("\n\ntheorem idle : Obl.idle") && checks.contains(s"set_option maxHeartbeats ${Generate.TryHeartbeats} in\ntheorem clash"), checks)
    assertEquals(g.trusted.map(_.id), List("Pick"))
  }

  test("a definition with an alternative: both stay, as alternatives, and what uses the term waits for the choice") {
    val thick = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
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
    val m = Param[Int => Int]("m", "a bound")
    val clash = Node.claim("Clash", "s", "w")(forall((x: Int) => m(x) >= 0))
    assert(Generate.problems(KnowledgeBase("K", "IDEA.md")(clash)).exists(_.contains("reserved")))
  }

  test("impl is proven from the promises of the operations its code calls, not those a term it reads is defined with") {
    // Again's code reads pickedFrom, defined by the shelf service's operation: it depends on PickPromise, calls nothing
    val g = Generate(readsKb)
    assertEquals(g.callees(againC).map(_.id), List("PickPromise"))
    assertEquals(g.calls(againC), Nil)
    assert(!g.obligation(againC, "impl").get.statement.contains("h_PickPromise"), g.obligation(againC, "impl"))
    // code calling the operation itself is proven from its promise
    val c = Generate(callsKb)
    assertEquals(c.calls(againC).map(_.id), List("PickPromise"))
    assert(c.obligation(againC, "impl").get.statement.contains("h_PickPromise"), c.obligation(againC, "impl"))
  }

  test("proof files may contain only tactic proofs") {
    val ok = Generate(squareKb).proofFile(nonNegative).replace("sorry", "simp")
    assertEquals(Lean.violations(ok), Nil)
    val bad = "import Lean\nrun_cmd do pure ()\nset_option debug.skipKernelTC true\nattribute [simp] foo\n#eval 1\ntheorem complete : Obl.complete := by simp\n"
    assertEquals(Lean.violations(bad).map(_._2).toSet,
      Set("import", "command run_cmd", "metaprogram", "set_option", "command attribute", "attribute", "command #eval"))
    assert(Lean.violations("set_option\n  debug.skipKernelTC true\n").nonEmpty)
  }

  test("a node is witnessed by proven code, an assumption, or parts that all are; a part nothing proves witnesses nothing") {
    val unrefined = Node.claim("Unrefined", "Some books are kept aside.", why = "A part not refined yet.")(
      forall((l: List[Item.T], x: Item.T) => shown(l, x) ==> l.contains(x))).under(onlyGood)
    val g = Generate(KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick :+ unrefined)*).implementProven(pick)(longOnes))
    assert(g.witnessed(pick) && g.witnessed(fromList))
    assert(!g.witnessed(unrefined))
    assert(!g.witnessed(onlyGood)) // one of its parts has no witness, though the others have proven code
  }
