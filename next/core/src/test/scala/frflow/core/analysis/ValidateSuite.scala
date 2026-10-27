package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.code.Code
import frflow.core.name.{NodeId, SymbolName}
import scala.compiletime.constValueTuple
import scala.deriving.Mirror

/** Every problem `Validate` can report, each by name on a theory with that one thing wrong; the theories they are
  * made from are valid; and every problem of a theory is reported at once.
  */
class ValidateSuite extends munit.FunSuite:
  private val cases = GraphCases.all ++ OutsideCases.all ++ ValueCases.all ++ FailureCases.all

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

  test("the theories the cases change are valid: the store's, a root alone, parts of a node proven of code, " +
    "the store that may be down with a failing run's clause of its type") {
    assertEquals(Store.kb.problems, Nil)
    assertEquals(FailureCases.claiming(FailureCases.down, frflow.core.ty.Ty.Str).problems, Nil)
    assertEquals(Store.kb.and(FailureCases.sameWorld).problems, Nil)
    assertEquals(Kb.of(plain("root")).problems, Nil)
    assertEquals(ValueCases.proven.without("stray").problems, Nil)
  }

  test("a model named as its boundary's class, its namespace in Lean, is declared twice") {
    val clashing = Store.kb.declaring(v => v.copy(models = v.models.map(_.copy(name =
      frflow.core.name.ModelName("bookings")))))
    assert(clashing.problems.contains(Problem.DeclaredTwice("Bookings")), clashing.problems)
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

  test("a premise missing that no assumption says names none") {
    assertEquals(Store.kb.without("oneAtATime").problems,
      List(Problem.PremiseMissing(NodeId("bookRuns"), Premise.OneRunAtATime(Store.model), None)))
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

  /** `always[Booking]`: every booking ends after it starts, claimed or assumed. */
  private def always(id: String, claimed: Boolean) =
    val b = frflow.core.term.Bound[Booking]("b", Booking.ty)
    val f = Lang.formula([T[_]] => (l: Lang[T]) => l.s.always[Booking](b)(_ => l.truth))
    if claimed then claim(id)(f) else assumption(id)(f)

  private def fromOutside(ps: List[Problem]) = ps.collect {
    case p @ Problem.PremiseMissing(_, Premise.FromOutside(_), _) => p
    case p: Problem.PremiseNotNeeded                             => p
  }

  test("values of a type from outside (owner §21): an always of it rests on an assumption of always on it") {
    val claimed = Store.kb.and(always("endsAfterStart", claimed = true))
    val needs = Premise.FromOutside(Booking.ty)
    assert(Premises.of(claimed.theory, NodeId("endsAfterStart")).contains(needs))
    assertEquals(fromOutside(claimed.problems), List(Problem.PremiseMissing(NodeId("endsAfterStart"), needs, None)))
    val assumed = claimed.and(always("fromTheDesk", claimed = false))
    // The store's contents are guarded by it too, so the program's claim rests on it as well.
    assertEquals(fromOutside(assumed.problems), List("bookRuns", "endsAfterStart").map(id =>
      Problem.PremiseMissing(NodeId(id), needs, Some(NodeId("fromTheDesk")))))
    assertEquals(fromOutside(assumed.linking(assumes("endsAfterStart", "fromTheDesk"))
      .linking(assumes("bookRuns", "fromTheDesk")).problems), Nil)
  }

  test("an assumption of always is kept where a claim of it is: by the programs storing its values (owner §21)") {
    val kb = Store.kb.and(always("endsAfterStart", claimed = true), always("fromTheDesk", claimed = false))
    val scope = List("endsAfterStart", "fromTheDesk").map(id => Scope.of(kb.theory, NodeId(id)))
    assert(scope.head.nonEmpty, scope)
    assertEquals(scope.last, scope.head)
  }

  test("an assumption of always listed where no check rests on it is not needed") {
    val kb = Store.kb.and(always("fromTheDesk", claimed = false), plain("unrelated"))
      .linking(assumes("unrelated", "fromTheDesk")).linking(assumes("bookRuns", "fromTheDesk"))
    assertEquals(fromOutside(kb.problems), List(Problem.PremiseNotNeeded(NodeId("unrelated"), NodeId("fromTheDesk"))))
  }
