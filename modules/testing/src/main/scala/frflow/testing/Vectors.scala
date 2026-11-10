package frflow.testing

import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.expr.Value
import frflow.core.name.{DefName, SourceText}
import frflow.core.spec.Written
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.dsl.lifted.Lifted
import frflow.eval.{Fn, ScalaValue}
import frflow.eval.term.Semantics
import frflow.testing.derive.Derive
import frflow.testing.report.Seed
import scala.util.Try

/** Lifted code's Scala as examples: for each generated case, the fact that the code, called on the case's inputs,
  * gives what its Scala gave (`noOverlap(("Oak", 9, 10), ("Oak", 10, 11)) is true`). Checked as any example is, the
  * evaluator runs each on the term read and Lean decides each from the `def` printed from it: with `Agreement`, the
  * Scala, the term and the Lean are held to one value case by case, so neither the reader nor the printer is
  * trusted for the cases drawn. Of code the model's statements do not mention, none (Lean has no `def` of it).
  */
object Vectors:
  /** A constant of the term language: the Scala value, the data it is, its type. */
  private final case class Lit(scala: ScalaValue, value: Value, ty: Ty):
    def on[T[_]](s: Sym[T]): T[Any] = s.lit(scala.unwrap, value, ty)

  def of(e: Elaborated, code: Lifted[?], settings: Settings): List[Example] =
    e.theory.vocabulary.define(DefName(code.name.value)).toList.flatMap { d =>
      val (semantics, draw, types) = (Semantics(e), Derive.of(e, Nil), d.lambda.params.map(_.ty))
      val drawn = (0 until settings.cases).toList.flatMap(i =>
        draw.all(types, Seed.sizeOf(i, settings.cases), settings.seed.forCase(i))).distinct
      drawn.flatMap { args =>
        val ins = args.zip(types).map((a, ty) => Lit(ScalaValue(a), semantics.reflect(ScalaValue(a), ty), ty))
        Try(Fn.call(Fn.ref(ScalaValue(code.native)), ins.map(_.scala))).toOption.map(r =>
          ins -> Lit(r, semantics.reflect(r, d.lambda.result), d.lambda.result))
      }.zipWithIndex.map { case ((ins, out), i) => example(code, ins, out, i) }
    }

  private def example(code: Lifted[?], ins: List[Lit], out: Lit, at: Int): Example =
    val says = s"${code.name.value}(${ins.map(_.scala.unwrap).mkString(", ")}) is ${out.scala.unwrap}"
    Example(says, Nil, Written.formula(fact(code, ins, out), SourceText(says)), s"${code.name.value}Scala", at)

  /** The code applied to the inputs, one at a time (a define's term is its curried function, whatever Scala types
    * the Definition by: the casts name that), and what it gives: a truth value as the fact or its negation, as an
    * example's `is true` and `is false` are; any other value by equality.
    */
  private def fact(code: Lifted[?], ins: List[Lit], out: Lit): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    val called = ins.foldLeft(code.run(s).asInstanceOf[T[Any]])((f, a) =>
      s.app(f.asInstanceOf[T[Any => Any]], a.on(s)))
    out.value match
      case Value.Bool(true)  => called.asInstanceOf[T[Boolean]]
      case Value.Bool(false) => s.not(called.asInstanceOf[T[Boolean]])
      case _                 => s.eq(called, out.on(s))
