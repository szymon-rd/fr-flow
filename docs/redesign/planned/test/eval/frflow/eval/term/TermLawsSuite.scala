package frflow.eval.term

import frflow.*
import frflow.core.code.{CodeTable, Values}
import frflow.core.{Elaborated, Theory}
import frflow.core.expr.{Binder, Exprs}
import frflow.core.name.{KbName, SourceText, VarId}
import frflow.core.spec.Written
import frflow.core.term.interpret.{Hypotheses, PartialEval, ToExpr}
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary
import frflow.dsl.term.Lift
import frflow.eval.{Env, ScalaValue, Semantics}
import scala.util.Random

/** The laws of the term interpreters, on generated terms that use every algebra: the examples' path (a written lambda,
  * its inputs bound at their levels) means what the evaluator gives the same term over constants; constant folding
  * keeps every value; the IR the analyses read is typed as the term is.
  */
class TermLawsSuite extends munit.FunSuite:
  private val env = Env.of(Values.none)
  private val terms = (1L to 300L).map(seed => Generated.formula(seed, 3)).toList
  private val semantics = Semantics(Elaborated(Theory(KbName("Laws"), Vocabulary(Nil, Nil, Nil, Nil, Nil, Nil), Nil,
    Nil, CodeTable(Map.empty, Map.empty)), Map.empty, Nil))

  test("a written lambda run on arguments, as examples run it, gives the term's value on them as constants") {
    val (x, s) = (Binder(VarId.level(0), "x", Ty.Num(frflow.core.ty.NumKind.Big)), Binder(VarId.level(1), "s",
      summon[LeanType[Slot]].ty))
    val (n, slot) = (BigInt(3), Slot("Oak", 1, 4))
    (1L to 200L).foreach { seed =>
      val opened = Generated(List(Term.free(x)), List(Term.free(s))).bool(Random(seed), 3)
      val closed = Generated(List(Lift.constant(n)), List(Lift.constant(slot))).bool(Random(seed), 3)
      val written = Written.lambda(List(x, s), opened.run, SourceText("…"))
      assertEquals(semantics.lambda(written).run(env, List(ScalaValue(n), ScalaValue(slot))).map(_.unwrap),
        Evaluate.of(closed.run)(env), closed.expr)
    }
  }

  test("constant folding keeps every term's value") {
    terms.foreach(t => assertEquals(PartialEval.of(t.run, Evaluate)(env), Evaluate.of(t.run)(env), t.expr))
  }

  test("the IR of every term is typed as the term: a formula's is Bool") {
    terms.foreach(t => assertEquals(Exprs.typeOf(t.expr), Ty.Bool, t.expr))
  }

  test("the generated terms reach every algebra (a match, folds, let, a record made and updated, defines, pairwise)") {
    val printed = terms.map(_.expr.toString).mkString
    List("Match(", "Fold(", "Let(", "Make(", "Copy(", "Call(", "Iterate(", "NoneP", "Outcome(", "Pairwise(", "Nodup")
      .foreach(c =>
      assert(printed.contains(c), c))
  }

  test("constant folding removes what is known: `1 < 2 && p` is `p`, `1 = 1 || p` is true") {
    val p = Slots.sound(Lift.constant(Slot("Oak", 1, 2)))
    assertEquals(PartialEval.of(((1: Term[BigInt]) < 2 && p).run, ToExpr)(0), p.expr)
    assertEquals(PartialEval.of(((1: Term[BigInt]) === 1 || p).run, ToExpr)(0), Lift.constant(true).expr)
  }

  test("`h1 implies (h2 implies c)` is split into its two hypotheses and its conclusion") {
    val (h1, h2, c) = (Generated.formula(1, 1), Generated.formula(2, 1), Generated.formula(3, 1))
    val (hs, conclusion) = Hypotheses.of((h1 implies (h2 implies c)).run, ToExpr)
    assertEquals((hs.map(_(0)), conclusion(0)), (List(h1.expr, h2.expr), c.expr))
  }

  test("`implies` binds last: `a && b implies c` is `(a && b) implies c`") {
    val (a, b, c) = (Generated.formula(4, 1), Generated.formula(5, 1), Generated.formula(6, 1))
    assertEquals((a && b implies c).expr, ((a && b) implies c).expr)
    assertNotEquals((a && b implies c).expr, (a && (b implies c)).expr)
  }

  test("a function value the evaluator makes, applied outside it where it has no value, fails as `d.fn` does") {
    val lam = Evaluate.lam[BigInt, Boolean](frflow.core.term.Bound("x", Ty.Num(frflow.core.ty.NumKind.Big)))(_ =>
      Evaluate.forall[BigInt](frflow.core.term.Bound("y", Ty.Num(frflow.core.ty.NumKind.Big)))(_ => Run.pure(true)))
    val escaped = lam(env).toOption.get
    assertEquals(intercept[frflow.eval.NotEvaluated](escaped(BigInt(1))).error, frflow.eval.EvalError.Quantified)
    assertEquals(Evaluate.app(lam, Run.pure(BigInt(1)))(env), Left(frflow.eval.EvalError.Quantified))
  }

  test("a binder of two variables notes both types: an either's error type, a fold's accumulator") {
    // a variable declares nothing, so only the binder can declare `Kind`
    def free[A: LeanType](i: Int) = Term.free[A](Binder(VarId.level(i), "v", LeanType[A].ty))
    val e = free[Either[Kind, BigInt]](0).fold(_ => True, _ => True)
    val f = Lift.constant(List(BigInt(1))).foldLeft(free[Option[Kind]](1))((acc, _) => acc)
    assert(List(e.notes, f.notes).forall(_.declares.types.keySet.exists(_.value == "Kind")), (e.notes, f.notes))
  }

  test("a bound variable run by an interpreter other than the one that bound it fails loudly") {
    val leaked = scala.collection.mutable.ListBuffer.empty[Term[BigInt]]
    val t = Lift.constant(List(BigInt(1))).exists { x => leaked += x; x === 1 }
    assertEquals(Evaluate.of(t.run)(env), Right(true))
    val e = intercept[IllegalStateException](leaked.head.expr)
    assert(e.getMessage.startsWith("FrFlow bug: a bound variable used outside its binder"), e.getMessage)
  }
