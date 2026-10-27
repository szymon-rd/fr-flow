package frflow.proof.lean.laws

import frflow.core.Booking
import frflow.core.expr.{Terms, Tm}
import frflow.core.name.SourceText
import frflow.core.spec.Written
import frflow.core.term.Final
import frflow.core.term.interpret.{Hypotheses, PartialEval, Split}
import frflow.proof.lean.ast.{LBinder, LExpr}
import frflow.proof.lean.lower.{LowerProp, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.{LeanTerm, Printed, Scope}
import frflow.proof.obligation.Prop
import frflow.proof.terms.TermTable

/** The laws of the one Lean printer of terms (`Printed`, `LeanTerm`), on generated terms reaching every algebra
  * (core's `Terms`, and `MoreTerms` for sums, eithers, pairs and runs): its text reads back as the Lean it printed;
  * printed through the transformers, the term is the same term; an obligation's formula is printed by it.
  */
class PrinterLawsSuite extends munit.FunSuite:
  private val naming = Naming.over(Set.empty, Set(Booking.name.value, MoreTerms.eventName.value, "World"))
  private val terms: List[Final[Boolean]] =
    (1L to 300L).toList.flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))
  private def printed(t: Final[Boolean]): String = Print.expr(Printed.formula(LawsEnv.env, naming)(t))
  private val term = LeanTerm(LawsEnv.env)

  test("every printed term reads back as the Lean it is: print, read, print gives the same text") {
    terms.foreach { t =>
      val text = printed(t)
      assertEquals(Print.expr(LeanReader(text).read()), text)
    }
  }

  test("split into its hypotheses, a term printed whole is the term printed") {
    terms.foreach { t =>
      val (_, conclusion) = Hypotheses.of(t, term)
      val whole = t[[a] =>> Split[LeanTerm.S, a]](Hypotheses(term)).whole
      assertEquals(Print.expr(whole(Scope(0, naming))), printed(t))
      assert(Print.expr(conclusion(Scope(0, naming))).nonEmpty)
    }
  }

  test("folded before printing, a term reads back too, and is never longer") {
    terms.foreach { t =>
      val text = Print.expr(PartialEval.of(t, term)(Scope(0, naming)))
      assertEquals(Print.expr(LeanReader(text).read()), text)
      assert(text.length <= printed(t).length, text)
    }
  }

  test("an obligation's formula is printed by the term printer, its open terms told") {
    val table = TermTable(Map.empty, Map.empty, Map.empty, Map.empty)
    terms.take(20).foreach { t =>
      val formula = Prop.Formula(Written.formula(t, SourceText("")))
      assertEquals(Print.expr(LowerProp(table, LawsEnv.env).statement(formula)), printed(t))
    }
  }

  test("the reader reads structure, and refuses what the printer cannot write") {
    val read = LeanReader("(∀ x ∈ rooms, (∀ x_1 ∈ bookings, (¬(x = x_1.room))))").read()
    read match
      case LExpr.Paren(LExpr.Forall(List(LBinder.Member(x, _)), LExpr.Paren(LExpr.Forall(List(LBinder.Member(y, _)),
          _)))) => assertEquals((x.text, y.text), ("x", "x_1"))
      case other => fail(s"not two membership binders: $other")
    List("(a ∧ b", "a ∧ b ∧ c").foreach(t => assert(scala.util.Try(LeanReader(t).read()).isFailure, t))
  }
