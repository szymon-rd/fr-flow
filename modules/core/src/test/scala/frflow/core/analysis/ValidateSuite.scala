package frflow.core.analysis

import frflow.core.analysis.outside.{Premise, Premises}
import frflow.core.analysis.outside.Scope
import frflow.core.analysis.resolution.Resolve
import frflow.core.{Booking, Desk, Kb, Lang}
import frflow.core.code.Code
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.Nodes.*
import scala.compiletime.constValueTuple
import scala.deriving.Mirror

/** Every problem `Validate` can report, each by name on a theory with that one thing wrong; the theories they are
  * made from are valid; and every problem of a theory is reported at once.
  */
class ValidateSuite extends munit.FunSuite:
  private val cases = GraphCases.all ++ OutsideCases.all ++ ValueCases.all

  private inline def caseNames[A](using m: Mirror.SumOf[A]): List[String] =
    constValueTuple[m.MirroredElemLabels].toList.map(_.toString)

  test("every case of Problem has a theory that triggers it") {
    assertEquals(cases.map(_.name).sorted, caseNames[Problem].sorted)
  }

  cases.foreach { c =>
    test(s"${c.name}: reported, and nothing else") {
      assertEquals(c.kb.problems, c.expected)
      assert(c.expected.forall(_.productPrefix == c.name), c.expected)
    }
  }

  test("the theories the cases change are valid: the desk's, a root alone, parts of a node proven of code") {
    assertEquals(Desk.kb.problems, Nil)
    assertEquals(Kb.of(plain("root")).problems, Nil)
    assertEquals(ValueCases.proven.without("stray").problems, Nil)
  }

  test("a Scala Int is said to exist only where a forall reads as an exists; every Int compares, none is a BigInt") {
    val int = frflow.core.ty.Ty.Num(frflow.core.ty.NumKind.Int32)
    def problems(f: [T[_]] => Lang[T] => T[Boolean]): List[Problem] = Kb.of(claim("c")(Lang.formula(f))).problems
    val all: [T[_]] => Lang[T] => T[Boolean] = [T[_]] => (l: Lang[T]) => l.forall[Int]("x", int)(x => l.s.eq(x, x))
    val said = List(Problem.SaidToExist(int, Problem.Place.Variable(NodeId("c"))))
    assertEquals(problems(all), Nil)
    assertEquals(problems([T[_]] => (l: Lang[T]) => l.s.implies(all(l), l.truth)), said)
    assertEquals(problems([T[_]] => (l: Lang[T]) => l.s.and(l.truth, l.s.not(all(l)))), said)
    assertEquals(problems([T[_]] => (l: Lang[T]) => l.s.not(l.forall[BigInt]("x", Lang.big)(x => l.s.eq(x, x)))), Nil)
    assertEquals(problems([T[_]] => (l: Lang[T]) => l.s.not(l.s.all(l.sym[List[Int]]("xs", frflow.core.ty.Ty.ListOf(
      int)), frflow.core.term.Bound[Int]("x", int))(x => l.s.eq(x, x)))).filter(_.productPrefix == "SaidToExist"), Nil)
  }

  test("a value named as a hypothesis (h_<node>, m_…, o_<value>_<i>) and a node named as a module are reserved") {
    val named = Kb.of(plain("top"), plain("part")).linking(partOf("part", "top")).naming(
      declaration("h_part", Lang.big), declaration("limit", Lang.big), declaration("o_limit_0", Lang.big),
      declaration("m_top_limit", Lang.big), declaration("m_limit", Lang.big), declaration("o_limit_x", Lang.big))
    assertEquals(named.problems.collect { case Problem.ReservedName(n) => n },
      List("h_part", "o_limit_0", "m_top_limit", "m_limit"))
    val modules = Kb.of(plain("Whole"), plain("Lemmas"), plain("at")).linking(partOf("Lemmas", "Whole"),
      partOf("at", "Whole"))
    assertEquals(modules.problems.collect { case Problem.ReservedName(n) => n }, List("Whole", "Lemmas", "at"))
  }

  test("claims about the same code rest on no circle, siblings or part and whole: neither relies on the other") {
    List(ValueCases.siblings, ValueCases.siblings.linking(partOf("fAboveToo", "fAbove"))).foreach { kb =>
      assertEquals(kb.problems, Nil)
      val r = Resolve(Validate(kb.elaborated).toOption.get)
      assertEquals(List("fAbove", "fAboveToo").map(n => r.reliesOn(NodeId(n))), List(Nil, Nil))
    }
  }

  test("a claim on code calling a Definition rests on the claims about it, and what is proven from what has no " +
    "circle") {
    val r = Resolve(Validate(ValueCases.proven.elaborated).toOption.get)
    assertEquals((r.reliesOn(NodeId("aboutFree")), r.provenFrom(NodeId("top"))), (Nil,
      List(NodeId("aboutFree"), NodeId("stray"))))
    assertEquals(Resolve.circles(ValueCases.mutual.theory), List(List(NodeId("aboutF"), NodeId("aboutG"))))
  }

  test("a node proven of code relies on no part of its own: its parts rest on it and are decided after it") {
    val r = Resolve(Validate(ValueCases.proven.elaborated).toOption.get)
    assert(!r.reliesOn(NodeId("top")).contains(NodeId("aboutFree")), r.reliesOn(NodeId("top")))
    assert(!r.restsOn(NodeId("top")).contains(NodeId("aboutFree")), r.restsOn(NodeId("top")))
  }

  test("an empty theory has no root to miss") {
    assertEquals(Kb.empty.problems, Nil)
  }

  test("a value only plain code reads needs no statement: it is no code without a claim") {
    val connection = SymbolName("connection")
    assertEquals(Kb.of(plain("root")).naming(codeOnly("connection")).coding(connection -> Code.Provided).problems, Nil)
  }

  test("a value with no Lean type given other code than a provided value is code without a claim") {
    val connection = SymbolName("connection")
    assertEquals(Kb.of(plain("root")).naming(codeOnly("connection"))
      .coding(connection -> Code.Proven(frflow.core.name.DefName("connect"))).problems,
      List(Problem.CodeWithoutClaim(connection)))
  }

  test("every problem is reported at once, in the order of the rules") {
    val kb = Kb.of(plain("a"), plain("a"), design("layout")).naming(definition("granted", frflow.core.Lang.big))
    assertEquals(kb.problems, List(Problem.DuplicateId(NodeId("a")), Problem.DesignWithoutParent(NodeId("layout")),
      Problem.Undefined(SymbolName("granted"))))
  }

  private def fromOutside(ps: List[Problem]) = ps.collect {
    case p @ Problem.PremiseMissing(_, Premise.FromOutside(_), _) => p
    case p: Problem.PremiseNotNeeded                             => p
  }

  test("values of a type from outside (owner §21): an always of it rests on an assumption of always on it") {
    val claimed = Desk.kb.and(always("endsAfterStart", claimed = true))
    val needs = Premise.FromOutside(Booking.ty)
    assert(Premises.of(claimed.theory, NodeId("endsAfterStart")).contains(needs))
    assertEquals(fromOutside(claimed.problems), List(Problem.PremiseMissing(NodeId("endsAfterStart"), needs, None)))
    val assumed = claimed.and(always("fromTheDesk", claimed = false))
    // The desk's claim quantifies over bookings, guarded by it too, so it rests on it as well.
    assertEquals(fromOutside(assumed.problems), List("bookRuns", "endsAfterStart").map(id =>
      Problem.PremiseMissing(NodeId(id), needs, Some(NodeId("fromTheDesk")))))
    assertEquals(fromOutside(assumed.linking(assumes("endsAfterStart", "fromTheDesk"))
      .linking(assumes("bookRuns", "fromTheDesk")).problems), Nil)
  }

  test("an assumption of always is kept where a claim of it is: by the Definitions making its values (owner §21)") {
    val kb = Desk.kb.naming(definition("latest", frflow.core.ty.Ty.FnOf(List(Lang.big), Booking.ty)))
      .and(always("endsAfterStart", claimed = true), always("fromTheDesk", claimed = false))
    val scope = List("endsAfterStart", "fromTheDesk").map(id => Scope.of(kb.theory, NodeId(id)))
    assert(scope.head.nonEmpty, scope)
    assertEquals(scope.last, scope.head)
  }

  test("an assumption of always listed where no check rests on it is not needed") {
    val kb = Desk.kb.and(always("fromTheDesk", claimed = false), plain("unrelated"))
      .linking(assumes("unrelated", "fromTheDesk")).linking(assumes("bookRuns", "fromTheDesk"))
    assertEquals(fromOutside(kb.problems), List(Problem.PremiseNotNeeded(NodeId("unrelated"), NodeId("fromTheDesk"))))
  }
