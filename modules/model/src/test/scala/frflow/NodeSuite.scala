package frflow

import frflow.fixtures.*

/** Nodes, the FrModel's queries, and the structural problems that keep it from being checked. */
class NodeSuite extends munit.FunSuite:

  test("the FrModel is well formed: one root, parts under it, definitions beside") {
    assertEquals(shelfKb.problems, Nil)
    assertEquals(shelfKb.root.map(_.id), Some("OnlyGood"))
    assertEquals(shelfKb.params.map(_.name), List("good", "minPages", "picks", "shown"))
  }

  test("a formula in a block of its own reads from its first line, as one written inline does") {
    val claim = Node.claim("Every number is itself."):
      forall((x: Term[BigInt]) =>
        x === x)
    assertEquals(claim.formula.map(_.source), Some("forall((x: Term[BigInt]) =>\n  x === x)"))
    assertEquals(claim.why, "")
  }

  test("examples where nothing is bound take one list: the same cases as with an empty list of bindings") {
    val base = Node.contract("s", "w")(forall((shelf: Term[List[Book]], n: Term[Int]) => picks(shelf, n).length <= n)).refines(onlyGood)
    // (with one list, the cases are typed before the overload is chosen: an empty list says its type)
    val none = List.empty[Book]
    val one = base.examples(allows(none, 1, none, "nothing to pick"), forbids(none, 0, List(Book("A", 1)), "never more than asked"))
    val two = base.examples()(allows(Nil, 1, Nil, "nothing to pick"), forbids(Nil, 0, List(Book("A", 1)), "never more than asked"))
    assertEquals(one.cases.map(c => (c.describe, c.bindings, c.inputs, c.result, c.expected)),
      two.cases.map(c => (c.describe, c.bindings, c.inputs, c.result, c.expected)))
    // how often service checks a result is said with frflow.* alone
    assertEquals(one.checkedAtRunTime(RunCheck.Sampled(100)).runCheck, Some(RunCheck.Sampled(100)))
  }

  test("a contract's post has its operation's type") {
    assert(compileErrors("""frflow.Node.contract(frflow.fixtures.picks)("c", "w")((a: Int, b: Int, r: Int) => true)""").nonEmpty)
  }

  test("an assumption names its idea section, on a fact or on an operation") {
    val fact = Node.assumption("Readers ask for books of at least a page.", why = "An empty book is not a book.",
      idea = "Picking")(minPages >= 1)
    val port = Node.assumption(fetch)("The service returns books of the shelf.", why = "Books come from a service.", idea = "Picking")(
      (shelf, n, r) => r.forall(b => shelf.contains(b)))
    assertEquals((fact.ideaSection, port.ideaSection), ("Picking", "Picking"))
    assertEquals(port.op.map(_.name), Some("fetch"))
  }

  test("domain types keep structural equality, even through a trait") {
    val e = intercept[IllegalArgumentException](summon[LeanType[NodeSuite.PathCI]].lean)
    assert(e.getMessage.contains("structural equality"), e.getMessage)
  }

  test("a domain type that writes its own equality is refused; Scala's generated one is kept") {
    def refused[T](using t: LeanType[T]): String = intercept[IllegalArgumentException](t.lean).getMessage
    assert(refused[NodeSuite.TitleOnly].contains("TitleOnly redefines equals (in TitleOnly): domain types must keep structural equality"))
    assert(refused[NodeSuite.Hashed].contains("Hashed redefines hashCode"))
    assert(refused[NodeSuite.Loose].contains("Loose redefines equals"))
    // an equals that reads every field does what the generated one does
    assertEquals(summon[LeanType[NodeSuite.Careful]].lean, "NodeSuite.Careful")
    assertEquals(summon[LeanType[Book]].lean, "Book")
    assertEquals(summon[LeanType[Shelf]].lean, "Shelf")
  }

  test("a cross-cutting invariant is a claim kept by the contracts that name it, on examples, generated calls and at run time") {
    val atMostN = Node.invariant[Int, Int]("No more books are picked than asked for.", "Readers carry what they asked for.")(
      (asked, picked) => picked <= asked).refines(onlyGood)
    val kept = Node.contract("Picking returns only long enough books.", "w")(forall((shelf: Term[List[Book]], n: Term[Int]) => picks(shelf, n).forall(b => shelf.contains(b) && b.pages >= minPages))).refines(shelfParts*)
      .examples(minPages.bind(100))(
        allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        allows(List(Book("Short", 20)), 1, Nil, "no long book"),
        forbids(List(Book("Short", 20)), 1, List(Book("Short", 20)), "never a short one"))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
    val kb = shelfWith(kept, atMostN).implementTested(kept)((s, n) => s.filter(_.pages >= minPages.value).take(n))
    assertEquals(kb.problems, Nil)
    // keeping makes the contract a part of the invariant
    assertEquals(kb.parts(atMostN).map(_.id), List("Kept"))
    assert(kb.exampleResults(kept).forall(_.implementation.contains("ok")), kb.exampleResults(kept))
    // every long book, twice: meets the post, breaks the invariant when one is asked for
    val bad =
      kb.implementTested(kept)((s, n) => s.filter(_.pages >= minPages.value) ++ s.filter(_.pages >= minPages.value))
    val broken = bad.testedWith(TestSettings(300)).test(kept).flatMap(_.failure)
    assert(broken.exists(_.why.contains("breaks the invariant AtMostN")), broken)
    val run = bad.service(kept)(minPages.bind(100))
    intercept[ContractViolation](run(List(Book("Long", 300)), 1))
    // every contract whose result can hold what the rule is about keeps it or says why not; an invariant nobody keeps is a problem
    val fromShelf = Node.invariant[List[Book], Book]("Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).refines(onlyGood)
    val unkept = shelfWith(pick, fromShelf).problems.map(_.message)
    assert(unkept.exists(_.contains("no contract keeps")), unkept)
    assert(unkept.exists(_.startsWith("Pick: keep FromShelf")), unkept)
    val exempt = shelfWith(pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b))), kept.exempt(fromShelf, "the shelf is checked by Pick"), fromShelf, atMostN)
    assertEquals(exempt.problems, Nil)
    // a rule about numbers does not reach a contract that returns books
    assert(!shelfWith(pick, kept, atMostN).problems.exists(_.message.startsWith("Pick: keep AtMostN")))
    // an invariant scoped to another subtree does not apply
    val scoped = Node.invariant[List[Book], Book]("s", "w", scope = List(everyLong))((shelf, b) => shelf.contains(b)).refines(onlyGood)
    assert(shelfWith(pick, scoped).problems.exists(_.message.startsWith("Pick: keep Scoped")))
  }

  test("the DAG's queries: parents, parts, ancestors nearest first, the root") {
    assertEquals(shelfKb.children(fromList).map(_.id), List("Pick"))
    assertEquals(shelfKb.ancestors(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong", "OnlyGood"))
    // a parent outside the FrModel is not one of its parents
    assertEquals(FrModel("K", "IDEA.md")(fromList).parentsOf(fromList), Nil)
  }

  test("the vocabulary's queries: the definitions a node uses, the terms it reads, the operations its code calls") {
    assertEquals(shelfKb.definitionsUsed(pick, shelfKb.inForce(_ => false)).map(_.id), Nil)
    assertEquals(shelfKb.reads(pick.post.get), List("minPages"))
    assertEquals(callsKb.calledBy(Again.again).map(_.id), List("PickPromise"))
    assertEquals(callsKb.opsCalledBy(viaPick), List("picks"))
    assertEquals((shelfKb.types.map(_.name), shelfKb.opaques.map(_.name), callsKb.defs.map(_.name)), (List("Book"), List("Item"), List("longOnes", "viaPick")))
  }

  test("structure: one root, no cycles, a part under the nodes it proves, a design under what it serves") {
    val other = Node.claim("s", "w")(forall((x: Term[BigInt]) => sq(x) >= 0))
    // several roots, each a claim no node is above: the author keeps the set small
    assertEquals(shelfWith(pick, other).roots.map(_.id), List("OnlyGood", "Other"))
    assertEquals(shelfWith(pick, other).problems, Nil)
    assert(FrModel("K", "IDEA.md")(fromList).problems.exists(_.message.contains("a root is required")))
    // a contract no code calls and nothing is above
    assert(shelfWith(pick, pickPromise).problems.exists(_.message.startsWith("PickPromise has no parents")))
    val loose = Node.design("Shelves are cached.", "They change once a day.")()
    assert(shelfWith(pick, loose).problems.exists { case Problem.Structure(t) => t.startsWith("Loose: a design decision is under"); case _ => false })
    intercept[IllegalArgumentException](books.refines(onlyGood))
    // (a node names its parents when it is built, from nodes built before it: no cycle can be written)
  }

  test("a contract on a flow with parts may be the root: the service's purpose, made by its code from what it calls") {
    assertEquals(Service.kb().problems, Nil)
    assertEquals(Service.kb().root.map(_.id), Some("Sold"))
    // its parts are its statements below; the till's model is under it, not a statement
    assertEquals(Service.kb().parts(Service.sold).map(_.id), List("PricePositive"))
    assertEquals(Service.kb().children(Service.sold).map(_.id), List("PricePositive", "TillKept"))
    // its code makes it from its parts: without the proven flow there is nothing to make it
    val unproven = FrModel("Service", idea = "IDEA.md")(Service.sold, Service.pricePositive, Service.tillKept)
    assert(unproven.problems.exists(_.message.startsWith("Sold has parts: its flow makes it from them")), unproven.problems)
    // a claim with no parents beside it is a second root; the first root claim is the one the idea's lead is for
    val other = Node.claim("s", "w")(forall((x: Term[BigInt]) => sq(x) >= 0))
    val two = FrModel("Service", idea = "IDEA.md")(Service.sold, Service.pricePositive, Service.tillKept, other)
      .implementProven(Service.sold)(Service.selling)
      .implementTested(Service.pricePositive)(item => item.abs + 1)
    assertEquals((two.problems, two.roots.map(_.id), two.root.map(_.id)), (Nil, List("Sold", "Other"), Some("Other")))
    // a contract whose operation code calls is no root: it is what that code rests on
    assertEquals(callsKb.roots.map(_.id), List("PickedAgain"))
  }

  test("examples are not asked for: a contract with none, or with one result only, is no problem") {
    val lazyPick = Node.contract(picks)("s", "w")((_, _, picked) => picked.isEmpty).refines(shelfParts*)
      .examples(minPages.bind(100))(allows(Nil, 1, Nil, "nothing"), forbids(List(Book("L", 300)), 1, List(Book("L", 300)), "x"))
    assertEquals(shelfWith(lazyPick).problems.filter(_.isInstanceOf[Problem.Examples]), Nil)
  }

  test("a problem says what part of the model it is about, and prints as its message") {
    // two different parameters with one name
    object other:
      val minPages = Param[Int]("the pages a reader can carry")
    val clashing = Node.contract("s", "w")(forall((shelf: Term[List[Book]], n: Term[Int]) => picks(shelf, n).length <= other.minPages)).refines(shelfParts*)
    val c = shelfWith(clashing).problems
    assert(c.exists { case Problem.Vocabulary(t) => t.startsWith("two different parameters are named minPages"); case _ => false }, c)
    // a claim, a contract or an assumption may leave its reason to the decision; a design decision says why
    def sayWhy(n: Node[?]) =
      shelfWith(pick, n).problems.exists { case Problem.Wording(t) => t.contains("say why"); case _ => false }
    val noWhy = Node.claim("s")(forall((x: Term[BigInt]) => sq(x) >= 0)).refines(onlyGood)
    val factWithNoWhy = Node.assumption("s")(forall((x: Term[BigInt]) => sq(x) >= 0)).refines(onlyGood)
    val designWithNoWhy = Node.design("s", " ")().refines(onlyGood)
    assert(!sayWhy(noWhy))
    assert(!sayWhy(factWithNoWhy))
    assert(sayWhy(designWithNoWhy))
  }

  test("a definition: at least one term, none defined through itself, none an operation") {
    val n = Param[Int]("a count")
    val m = Param[Int]("another count")
    val ofM = Node.definition("n is m.", "w")(n := m)
    val ofN = Node.definition("m is n.", "w")(m := n)
    assert(shelfWith(pick, ofM, ofN).problems.exists(_.message == "OfM: its terms are defined through themselves"), shelfWith(pick, ofM, ofN).problems)
    val op = Node.definition("Picking is taking all.", "w")(picks := ((s: Term[List[Book]], k: Term[Int]) => s))
    assert(shelfWith(pick, op).problems.exists(_.message.startsWith("Op defines picks, an operation")))
  }

  test("code attached to something that is not a contract of the FrModel is a problem") {
    val kb = shelfWith(pick).withImplementation(Implementation("Nowhere", () => (), Nil))
    assert(kb.problems.exists { case Problem.Code(t) => t.startsWith("implementation of Nowhere"); case _ => false }, kb.problems)
  }

object NodeSuite:
  trait CaseInsensitive { override def equals(o: Any): Boolean = true; override def hashCode: Int = 0 }
  final case class PathCI(v: String) extends CaseInsensitive
  final case class TitleOnly(title: String, pages: Int):
    override def equals(o: Any): Boolean = o match { case b: TitleOnly => b.title == title; case _ => false }
    override def hashCode: Int = title.hashCode
  final case class Hashed(title: String):
    override def hashCode: Int = 0
  final case class Careful(title: String, pages: Int):
    override def equals(o: Any): Boolean = o match { case b: Careful => b.title == title && b.pages == pages; case _ => false }
    override def hashCode: Int = scala.util.hashing.MurmurHash3.caseClassHash(this)
  enum Loose:
    case A(x: String)
    override def equals(o: Any): Boolean = true
