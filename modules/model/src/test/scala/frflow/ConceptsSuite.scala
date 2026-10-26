package frflow

import frflow.fixtures.*
import frflow.testing.{Draw, Plan}

/** The core concepts: claims and assumptions, Definitions and Declarations, `forall` and `always`; and the words
  * statements are written with: `when … otherwise`, `:+`, a model's state in a world, a run's answer and world after.
  */
class ConceptsSuite extends munit.FunSuite:

  test("always of a type: what every value of it that can be made holds, assumed of what statements quantify over") {
    val kb = Invariants.shelf
    assertEquals(kb.problems, Nil)
    assertEquals(kb.invariantsOn(summon[LeanType[Book]]).map((n, _, each) => n.id -> each), List("HasPages" -> false))
    assertEquals(kb.invariantsOn(summon[LeanType[List[Book]]]).map((n, _, each) => n.id -> each),
      List("HasPages" -> true, "ShelvedOnce" -> false))
    // Pick quantifies over shelves of books: it assumes both, and is reviewed when either changes
    assertEquals(kb.invariantsUsedBy(pick).map(_.id), List("HasPages", "ShelvedOnce"))
    assert(kb.definitionsUsed(pick, kb.inForce(_ => false)).map(_.id).contains("ShelvedOnce"))
    // run as Scala
    assertEquals(List(Book("A", 0), Book("A", 3)).map(kb.holds(summon[LeanType[Book]])), List(false, true))
    assertEquals(kb.holds(summon[LeanType[List[Book]]])(List(Book("A", 3), Book("A", 3))), false)
  }

  test("tests draw only values that hold what always holds of their types") {
    val plan = Plan(Map.empty, Map.empty, Nil, Map.empty, holds = Invariants.shelf.holds)
    val shelves = (0 until 200).map(i => Draw(Testing.random(1, i), 5, plan).value(summon[LeanType[List[Book]]]))
    assert(shelves.forall(s => s.asInstanceOf[List[Book]].forall(_.pages > 0)), shelves)
    assert(shelves.forall(s => s.asInstanceOf[List[Book]].distinct.size == s.asInstanceOf[List[Book]].size), shelves)
    assert(shelves.exists(_.asInstanceOf[List[Book]].size > 1), shelves)
  }

  test("an assumption is a premise of what assumes it: below it in the DAG, and only an assumption is one") {
    val premise = Node.assumption("Prices are set by the shop.")(Service.price(BigInt(1)) > BigInt(0))
    val assumes = Node.claim("Some item costs something.")(Service.price(BigInt(1)) > BigInt(0)).assuming(premise)
    val kb = KnowledgeBase("Service")(assumes, premise)
    assertEquals((kb.parentsOf(premise).map(_.id), kb.roots.map(_.id)), (List("Assumes"), List("Assumes")))
    val notOne = intercept[IllegalArgumentException](premise.assuming(assumes))
    assert(notOne.getMessage.contains("a premise is an assumption"), notOne.getMessage)
  }

  test("a contract may name its operation over a claim's formula: the same post as the one found") {
    val named = Node.contract(Service.price)("Every item costs something.")(
      forall((item: Term[BigInt]) => Service.price(item) > BigInt(0)))
    assertEquals(named.op.map(_.name), Some("price"))
    assertEquals(named.post.map(_.lean), Service.pricePositive.post.map(_.lean))
  }

  test("when … otherwise, :+, a pair's equality and a model's state in a world, as Lean reads them") {
    val held = summon[LeanType[List[Book]]]
    val b = Term(Tree.Lit(Book("A", 3), summon[LeanType[Book]]), summon[LeanType[Book]])
    val xs = Term(Tree.Lit(Nil, held), held)
    assertEquals(leanOf(when(True)(xs :+ b).otherwise(xs)), "(if True then ([] ++ [(Book.mk \"A\" 3)]) else [])")
    val w = Term(Tree.Lit(World(), summon[LeanType[World]]), summon[LeanType[World]])
    assertEquals(Service.TillModel.in(w).termTree, w(Service.TillModel).termTree)
    val pairs = leanOf((True, xs) === (False, xs))
    assert(pairs.contains("((True, []) = (False, []))"), pairs)
  }

  test("always of a store: every program writing it is proven to keep it, and the store's start to meet it") {
    import Concepts.*
    assertEquals(kb.problems, Nil)
    assertEquals(kb.roots.map(_.id), List("Grows", "NeverNegative"))
    // the writer is the program, by the first claim its proven flow meets; a statement about a run assumes it
    assertEquals(kb.writers(neverNegative).map(_.id), List("Grows"))
    assertEquals(kb.invariantsUsedBy(grows).map(_.id), List("NeverNegative"))
    // the facts it rests on are decided, not stated in Lean
    assertEquals(List(writes, oneAtATime, startsAtNothing).map(kb.isStatement), List(false, false, false))
    assertEquals(startsAtNothing.initially.map(_.name), Some("startsAtNothing"))
  }

  test("a claim on one Definition is about every call of it; one on a flow, about every run") {
    import Concepts.*
    assertEquals((stepPositive.op.map(_.name), grows.op.map(_.name)), (Some("step"), Some("add")))
    assertEquals(grows.post.map(_.params.map(_._1)), Some(List("x", "result", "before", "after")))
    assertEquals(kb.claimsOn(step).map(_.id), List("StepPositive"))
  }

  test("a Definition gets a meaning from code, a Declaration never does, and no code uses one") {
    import Concepts.*
    val unmade =
      KnowledgeBase("Concepts")(grows, neverNegative, stepPositive, model, writes, oneAtATime, startsAtNothing)
      .implementProven(add)(adding)
    assert(unmade.problems.exists(_.message.startsWith("step is a Definition nothing defines")), unmade.problems)
    val idea = Declaration[BigInt => Boolean]("whether a request is welcome")
    val welcome =
      Node.claim("A request of size zero is welcome.")(forall((x: Term[BigInt]) => idea(x) === (x === BigInt(0))))
    val coded = KnowledgeBase("Idea")(welcome).implementTested(welcome)(x => x == 0)
    assert(coded.problems.exists(_.message.startsWith("idea is a Declaration")), coded.problems)
    assertEquals(KnowledgeBase("Idea")(welcome).problems, Nil)
  }

  test("an example written as a test is a Definition called on values, a case of every claim on it") {
    import Concepts.*
    val w = Written.of("three adds four", step(BigInt(3)) is BigInt(4), "Suite").toOption.get
    assertEquals((w.op.name, w.inputs, w.answer), ("step", List(BigInt(3)), BigInt(4)))
    assertEquals(kb.withWritten(List(w)).casesOf(stepPositive).map(_.note), List("three adds four"))
    assert(kb.withWritten(List(w)).exampleResults(stepPositive).forall(_.verdict == "ok"))
    assert(Written.of("not a call", step(BigInt(3)) + 1 is BigInt(5), "Suite").isLeft)
  }
