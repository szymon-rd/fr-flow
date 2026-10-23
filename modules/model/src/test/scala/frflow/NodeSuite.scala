package frflow

import frflow.fixtures.*

/** Nodes, the structure of the DAG and the knowledge base's queries, on the shelf fixture. */
class NodeSuite extends munit.FunSuite:

  test("the knowledge base is well formed: one root, parts under it, definitions beside") {
    assertEquals(shelfKb.problems, Nil)
    assertEquals(shelfKb.root.map(_.id), Some("OnlyGood"))
    // every node after what it rests on: the definitions it uses, its parents
    val order = shelfKb.ordered.map(_.id)
    assertEquals(order, List("Books", "Picking", "OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    assertEquals(shelfKb.params.map(_.name), List("good", "minPages", "picks", "shown"))
    assertEquals(shelfKb.definitions.map(_.id), List("Books", "Picking"))
  }

  test("a contract's post has its operation's type") {
    assert(compileErrors("""frflow.Node.contract(frflow.fixtures.picks)("C", "c", "w")((a: Int, b: Int, r: Int) => true)""").nonEmpty)
  }

  test("an assumption names its idea section, on a fact or on an operation") {
    val fact = Node.assumption("LongShelf", "Readers ask for books of at least a page.", why = "An empty book is not a book.",
      idea = "Picking")(minPages.value >= 1)
    val port = Node.assumption(fetch)("Port", "The service returns books of the shelf.", why = "Books come from a service.", idea = "Picking")(
      (shelf, n, r) => r.forall(b => shelf.contains(b)))
    assertEquals((fact.ideaSection, port.ideaSection), ("Picking", "Picking"))
    assertEquals(port.op.map(_.name), Some("fetch"))
  }

  test("domain types keep structural equality, even through a trait") {
    val errs = compileErrors("""
      trait CaseInsensitive { override def equals(o: Any): Boolean = true; override def hashCode: Int = 0 }
      final case class PathCI(v: String) extends CaseInsensitive
      frflow.Lifted((p: PathCI, q: PathCI) => p == q)
    """)
    assert(errs.contains("structural equality"), errs)
  }

  test("a cross-cutting invariant is a claim kept by the contracts that name it, on examples, generated calls and at run time") {
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "Readers carry what they asked for.")(
      (asked, picked) => picked <= asked).under(onlyGood)
    val kept = Node.contract(picks)("Kept", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(shelfParts*)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 1, Nil, "no long book"),
        reject(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
    val kb = shelfWith(kept, atMostN).implement(kept)((s, n) => s.filter(_.pages >= minPages.value).take(n))
    assertEquals(kb.problems, Nil)
    // keeping makes the contract a part of the invariant
    assertEquals(kb.parts(atMostN).map(_.id), List("Kept"))
    assert(kb.exampleResults(kept).forall(_.implementation.contains("ok")), kb.exampleResults(kept))
    // every long book, twice: meets the post, breaks the invariant when one is asked for
    val bad = kb.implement(kept)((s, n) => s.filter(_.pages >= minPages.value) ++ s.filter(_.pages >= minPages.value))
    assert(bad.exampleResults(kept).flatMap(_.implementation).exists(_.contains("breaks the invariant AtMostN")), bad.exampleResults(kept))
    val run = bad.service(kept)(minPages.bind(100))
    intercept[ContractViolation](run(List(Book("Long", 300)), 1))
    // every contract whose result can hold what the rule is about keeps it or says why not; an invariant nobody keeps is a problem
    val fromShelf = Node.invariant[List[Book], Book]("FromShelf", "Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).under(onlyGood)
    val unkept = shelfWith(pick, fromShelf).problems.map(_.message)
    assert(unkept.exists(_.contains("no contract keeps")), unkept)
    assert(unkept.exists(_.startsWith("Pick: keep FromShelf")), unkept)
    val exempt = shelfWith(pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b))), kept.exempt(fromShelf, "the shelf is checked by Pick"), fromShelf, atMostN)
    assertEquals(exempt.problems, Nil)
    // a rule about numbers does not reach a contract that returns books
    assert(!shelfWith(pick, kept, atMostN).problems.exists(_.message.startsWith("Pick: keep AtMostN")))
    // an invariant scoped to another subtree does not apply
    val scoped = Node.invariant[List[Book], Book]("Scoped", "s", "w", scope = List(everyLong))((shelf, b) => shelf.contains(b)).under(onlyGood)
    assert(shelfWith(pick, scoped).problems.exists(_.message.startsWith("Pick: keep Scoped")))
  }

  test("the DAG's queries: parents, parts, ancestors nearest first, the root") {
    assertEquals(shelfKb.parentsOf(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(shelfKb.parts(onlyGood).map(_.id), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(shelfKb.children(fromList).map(_.id), List("Pick"))
    assertEquals(shelfKb.ancestors(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong", "OnlyGood"))
    assertEquals(shelfKb.node("Pick").map(_.id), Some("Pick"))
    // a parent outside the knowledge base is not one of its parents
    assertEquals(KnowledgeBase("K", "IDEA.md")(fromList).parentsOf(fromList), Nil)
  }

  test("the vocabulary's queries: the definitions a node uses, the terms it reads, the operations its code calls") {
    assertEquals(shelfKb.definitionsUsed(pick, shelfKb.inForce(_ => false)).map(_.id), Nil)
    assertEquals(shelfKb.definitionsUsed(onlyGood, shelfKb.inForce(_ => false)).map(_.id), List("Books", "Picking"))
    assertEquals(shelfKb.reads(pick.post.get), List("minPages"))
    assertEquals(callsKb.calledBy(againC).map(_.id), List("PickPromise"))
    assertEquals(callsKb.opsCalledBy(viaPick), List("picks"))
    assertEquals(shelfKb.types.map(_.name), List("Book"))
    assertEquals(shelfKb.opaques.map(_.name), List("Item"))
    assertEquals(callsKb.defs.map(_.name), List("longOnes", "viaPick"))
  }
