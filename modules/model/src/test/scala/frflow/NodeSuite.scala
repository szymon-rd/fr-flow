package frflow

import frflow.fixtures.*

/** Nodes, the knowledge base's queries, and the structural problems that keep it from being checked. */
class NodeSuite extends munit.FunSuite:

  test("the knowledge base is well formed: one root, parts under it, definitions beside") {
    assertEquals(shelfKb.problems, Nil)
    assertEquals(shelfKb.root.map(_.id), Some("OnlyGood"))
    assertEquals(shelfKb.params.map(_.name), List("good", "minPages", "picks", "shown"))
  }

  test("a contract's post has its operation's type") {
    assert(compileErrors("""frflow.Node.contract(frflow.fixtures.picks)("C", "c", "w")((a: Int, b: Int, r: Int) => true)""").nonEmpty)
  }

  test("an assumption names its idea section, on a fact or on an operation") {
    val fact = Node.assumption("LongShelf", "Readers ask for books of at least a page.", why = "An empty book is not a book.",
      idea = "Picking")(minPages >= 1)
    val port = Node.assumption(fetch)("Port", "The service returns books of the shelf.", why = "Books come from a service.", idea = "Picking")(
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
    val atMostN = Node.invariant[Int, Int]("AtMostN", "No more books are picked than asked for.", "Readers carry what they asked for.")(
      (asked, picked) => picked <= asked).under(onlyGood)
    val kept = Node.contract(picks)("Kept", "Picking returns only long enough books.", "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages)).under(shelfParts*)
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
    val broken = bad.testedWith(TestSettings(300)).test(kept).flatMap(_.failure)
    assert(broken.exists(_.why.contains("breaks the invariant AtMostN")), broken)
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
    assertEquals(shelfKb.children(fromList).map(_.id), List("Pick"))
    assertEquals(shelfKb.ancestors(pick).map(_.id), List("FromList", "OnlyLong", "EveryLong", "OnlyGood"))
    // a parent outside the knowledge base is not one of its parents
    assertEquals(KnowledgeBase("K", "IDEA.md")(fromList).parentsOf(fromList), Nil)
  }

  test("the vocabulary's queries: the definitions a node uses, the terms it reads, the operations its code calls") {
    assertEquals(shelfKb.definitionsUsed(pick, shelfKb.inForce(_ => false)).map(_.id), Nil)
    assertEquals(shelfKb.reads(pick.post.get), List("minPages"))
    assertEquals(callsKb.calledBy(againC).map(_.id), List("PickPromise"))
    assertEquals(callsKb.opsCalledBy(viaPick), List("picks"))
    assertEquals((shelfKb.types.map(_.name), shelfKb.opaques.map(_.name), callsKb.defs.map(_.name)), (List("Book"), List("Item"), List("longOnes", "viaPick")))
  }

  test("structure: one root, no cycles, a part under the nodes it proves, a design under what it serves") {
    val other = Node.claim("Other", "s", "w")(forall((x: Term[BigInt]) => sq(x) >= 0))
    assert(shelfWith(pick, other).problems.exists(_.message.startsWith("one root only")), shelfWith(pick, other).problems)
    assert(KnowledgeBase("K", "IDEA.md")(fromList).problems.exists(_.message.contains("a root is required")))
    // a contract no code calls and nothing is above
    assert(shelfWith(pick, pickPromise).problems.exists(_.message.startsWith("PickPromise has no parents")))
    val loose = Node.design("Loose", "Shelves are cached.", "They change once a day.")()
    assert(shelfWith(pick, loose).problems.exists { case Problem.Structure(t) => t.startsWith("Loose: a design decision is under"); case _ => false })
    intercept[IllegalArgumentException](books.under(onlyGood))
    // (a node names its parents when it is built, from nodes built before it: no cycle can be written)
  }

  test("a contract's examples must tell a constant implementation apart") {
    val lazyPick = Node.contract(picks)("LazyPick", "s", "w")((_, _, picked) => picked.isEmpty).under(shelfParts*)
      .examples(minPages.bind(100))(expect(Nil, 1, Nil, "nothing"), reject(List(Book("L", 300)), 1, List(Book("L", 300)), "x"))
    assert(shelfWith(lazyPick).problems.exists(_.message.contains("always returns it")))
  }

  test("a problem says what part of the model it is about, and prints as its message") {
    // two different parameters with one name; a contract with no examples
    val clash = Param[Int]("minPages", "the pages a reader can carry")
    val c = shelfWith(Node.contract(picks)("Clash", "s", "w")((shelf, n, picked) => picked.length <= clash).under(shelfParts*)).problems
    assert(c.exists { case Problem.Vocabulary(t) => t.startsWith("two different parameters are named minPages"); case _ => false }, c)
    assert(c.exists(_.isInstanceOf[Problem.Examples]), c)
    val noWhy = Node.claim("NoWhy", "s", " ")(forall((x: Term[BigInt]) => sq(x) >= 0)).under(onlyGood)
    assert(shelfWith(pick, noWhy).problems.exists { case Problem.Wording(t) => t.contains("say why"); case _ => false })
  }

  test("a definition: at least one term, none defined through itself, none an operation") {
    val n = Param[Int]("n", "a count")
    val m = Param[Int]("m", "another count")
    val ofM = Node.definition("OfM", "n is m.", "w")(n := m)
    val ofN = Node.definition("OfN", "m is n.", "w")(m := n)
    assert(shelfWith(pick, ofM, ofN).problems.exists(_.message == "OfM: its terms are defined through themselves"), shelfWith(pick, ofM, ofN).problems)
    val op = Node.definition("Op", "Picking is taking all.", "w")(picks := ((s: Term[List[Book]], k: Term[Int]) => s))
    assert(shelfWith(pick, op).problems.exists(_.message.startsWith("Op defines picks, an operation")))
  }

  test("code attached to something that is not a contract of the knowledge base is a problem") {
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
