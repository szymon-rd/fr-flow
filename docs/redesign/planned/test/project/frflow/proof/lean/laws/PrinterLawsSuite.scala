package frflow.proof.lean.laws

import frflow.core.name.{KbName, SourceText}
import frflow.core.spec.Written
import frflow.core.term.interpret.{Hypotheses, PartialEval}
import frflow.core.ty.DataType
import frflow.dsl.term.LeanType
import frflow.eval.term.{Generated, Kind, Slot}
import frflow.proof.lean.ast.{LBinder, LExpr, Names}
import frflow.proof.lean.lower.{LowerEnv, LowerProp, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.{LeanTerm, Printed, Scope}
import frflow.proof.obligation.Prop
import frflow.proof.terms.TermTable

/** The laws of the one Lean printer of terms (`Printed`, `LeanTerm`), on the generated terms of the evaluator's laws
  * (every algebra): its text reads back as the Lean it printed; printed through the transformers, the term is the same
  * term; an obligation's formula is printed by it.
  */
class PrinterLawsSuite extends munit.FunSuite:
  private val data: Map[frflow.core.name.TypeName, DataType] =
    List(summon[LeanType[Slot]], summon[LeanType[Kind]]).flatMap(_.declares.types.values.flatten.map(_.data))
      .map(d => d.typeName -> d).toMap
  private val env = LowerEnv(KbName("Laws"), _ => Nil, _ => Names.builtin("database"), _ => Names.builtin("Database"),
    data.get)
  private val naming = Naming.over(Set.empty, data.keySet.map(_.value))
  private val terms = (1L to 300L).map(seed => Generated.formula(seed, 3)).toList
  private def printed(t: frflow.dsl.term.Term[Boolean]): String = Print.expr(Printed.formula(env, naming)(t.run))

  test("every printed term reads back as the Lean it is: print, read, print gives the same text") {
    terms.foreach { t =>
      val text = printed(t)
      assertEquals(Print.expr(LeanReader(text).read()), text)
    }
  }

  test("split into its hypotheses, a term printed whole is the term printed") {
    terms.foreach { t =>
      val (_, conclusion) = Hypotheses.of(t.run, LeanTerm(env))
      val whole = t.run[[a] =>> frflow.core.term.interpret.Split[LeanTerm.S, a]](Hypotheses(LeanTerm(env))).whole
      assertEquals(Print.expr(whole(Scope(0, naming))), printed(t))
      assert(Print.expr(conclusion(Scope(0, naming))).nonEmpty)
    }
  }

  test("folded before printing, a term reads back too, and is never longer") {
    terms.foreach { t =>
      val text = Print.expr(PartialEval.of(t.run, LeanTerm(env))(Scope(0, naming)))
      assertEquals(Print.expr(LeanReader(text).read()), text)
      assert(text.length <= printed(t).length, text)
    }
  }

  test("an obligation's formula is printed by the term printer, its open terms told") {
    val t = terms.head
    val table = TermTable(Map.empty, Map.empty, Map.empty, Map.empty)
    val formula = Prop.Formula(Written.formula(t.run, SourceText("")))
    assertEquals(Print.expr(LowerProp(table, env).statement(formula)), printed(t))
  }

  test("the reader reads structure, and refuses what the printer cannot write") {
    val read = LeanReader("(∀ x ∈ rooms, (∀ x_1 ∈ bookings, (¬(x = x_1.room))))").read()
    read match
      case LExpr.Paren(LExpr.Forall(List(LBinder.Member(x, _)), LExpr.Paren(LExpr.Forall(List(LBinder.Member(y, _)),
          _)))) => assertEquals((x.text, y.text), ("x", "x_1"))
      case other => fail(s"not two membership binders: $other")
    List("(a ∧ b", "a ∧ b ∧ c").foreach(t => assert(scala.util.Try(LeanReader(t).read()).isFailure, t))
  }
