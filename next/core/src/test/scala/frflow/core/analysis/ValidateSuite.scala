package frflow.core.analysis

import frflow.core.{Kb, Store}
import frflow.core.Nodes.*
import frflow.core.code.Code
import frflow.core.name.{NodeId, SymbolName}
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

  test("the theories the cases change are valid: the store's, a root alone, a part about what proven code calls") {
    assertEquals(Store.kb.problems, Nil)
    assertEquals(Kb.of(plain("root")).problems, Nil)
    assertEquals(ValueCases.proven.without("stray").problems, Nil)
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

  test("every problem is reported at once, in the order of the rules") {
    val kb = Kb.of(plain("a"), plain("a"), design("layout")).naming(definition("granted", frflow.core.Lang.big))
    assertEquals(kb.problems, List(Problem.DuplicateId(NodeId("a")), Problem.DesignWithoutParent(NodeId("layout")),
      Problem.Undefined(SymbolName("granted"))))
  }
