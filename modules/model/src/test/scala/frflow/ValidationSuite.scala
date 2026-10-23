package frflow

import frflow.fixtures.*

/** The structural problems that keep a knowledge base from being checked. */
class ValidationSuite extends munit.FunSuite:

  test("structure: one root, no cycles, a part under the nodes it proves, a design under what it serves") {
    val other = Node.claim("Other", "s", "w")(forall((x: BigInt) => sq(x) >= 0))
    assert(shelfWith(pick, other).problems.exists(_.message.startsWith("one root only")), shelfWith(pick, other).problems)
    assert(KnowledgeBase("K", "IDEA.md")(fromList).problems.exists(_.message.contains("a root is required")))
    // a contract no code calls and nothing is above
    assert(shelfWith(pick, pickPromise).problems.exists(_.message.startsWith("PickPromise has no parents")))
    val loose = Node.design("Loose", "Shelves are cached.", "They change once a day.")()
    assert(shelfWith(pick, loose).problems.exists(_.message.startsWith("Loose: a design decision is under")))
    intercept[IllegalArgumentException](books.under(onlyGood))
    // (a node names its parents when it is built, from nodes built before it: no cycle can be written)
  }

  test("two different parameters with one name are a problem") {
    val other = Param[Int]("minPages", "the pages a reader can carry")
    val c = Node.contract(picks)("Clash", "s", "w")((shelf, n, picked) => picked.length <= other.value).under(shelfParts*)
    assert(shelfWith(c).problems.exists(_.message.startsWith("two different parameters are named minPages")), shelfWith(c).problems)
  }

  test("every node says why") {
    val noWhy = Node.claim("NoWhy", "s", " ")(forall((x: BigInt) => sq(x) >= 0)).under(onlyGood)
    assert(shelfWith(pick, noWhy).problems.exists(_.message.contains("say why")))
  }

  test("a contract's examples must tell a constant implementation apart") {
    val lazyPick = Node.contract(picks)("LazyPick", "s", "w")((_, _, picked) => picked.isEmpty).under(shelfParts*)
      .examples(minPages.bind(100))(expect(Nil, 1, Nil, "nothing"), reject(List(Book("L", 300)), 1, List(Book("L", 300)), "x"))
    assert(shelfWith(lazyPick).problems.exists(_.message.contains("always returns it")))
  }

  test("a problem says what part of the model it is about, and prints as its message") {
    val ps = shelfWith(pick, Node.design("Loose", "Shelves are cached.", "They change once a day.")()).problems
    assert(ps.exists { case Problem.Structure(t) => t.startsWith("Loose: a design decision is under"); case _ => false }, ps)
    val p = Problem.Wording("X: empty statement")
    assertEquals((p.message, p.toString), ("X: empty statement", "X: empty statement"))
    val clash = Param[Int]("minPages", "the pages a reader can carry")
    val c = Node.contract(picks)("Clash", "s", "w")((shelf, n, picked) => picked.length <= clash.value).under(shelfParts*)
    assert(shelfWith(c).problems.exists(_.isInstanceOf[Problem.Vocabulary]), shelfWith(c).problems)
    assert(shelfWith(c).problems.exists(_.isInstanceOf[Problem.Examples]), shelfWith(c).problems)
  }

  test("a definition: at least one term, none defined through itself, none an operation") {
    val n = Param[Int]("n", "a count")
    val m = Param[Int]("m", "another count")
    val ofM = Node.definition("OfM", "n is m.", "w")(n := m.value)
    val ofN = Node.definition("OfN", "m is n.", "w")(m := n.value)
    assert(shelfWith(pick, ofM, ofN).problems.exists(_.message == "OfM: its terms are defined through themselves"), shelfWith(pick, ofM, ofN).problems)
    val op = Node.definition("Op", "Picking is taking all.", "w")(picks := ((s: List[Book], k: Int) => s))
    assert(shelfWith(pick, op).problems.exists(_.message.startsWith("Op defines picks, an operation")))
  }

  test("code attached to something that is not a contract of the knowledge base is a problem") {
    val kb = shelfWith(pick).withImplementation(Implementation("Nowhere", () => (), Nil))
    assert(kb.problems.exists { case Problem.Code(t) => t.startsWith("implementation of Nowhere"); case _ => false }, kb.problems)
  }
