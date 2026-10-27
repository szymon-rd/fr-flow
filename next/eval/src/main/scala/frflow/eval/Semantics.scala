package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.{Expr, Lambda, Value}
import frflow.core.spec.{Form, Written}
import frflow.core.term.Stated
import frflow.core.ty.Ty
import frflow.eval.term.Evaluate

/** The Scala semantics of a theory's parts, each run by the evaluator of terms (`Evaluate`, the only one): a formula, a
  * written lambda as a function of its arguments (its inputs bound at their levels), a program's term, and a constant
  * as Scala holds it (by its type, through the theory's `DataRep`s).
  */
final class Semantics(e: Elaborated):
  private val literals = Literals(e)
  private val reflected = Reflect(e)

  def term(s: Stated[?]): Env => Either[EvalError, ScalaValue] = env => Evaluate.of(s.run)(env).map(ScalaValue(_))
  def formula(w: Written[Expr]): Env => Either[EvalError, ScalaValue] = of(w.form)
  def lambda(w: Written[Lambda]): Applied =
    val run = of(w.form)
    Applied((env, args) => run(w.value.params.map(_.id).zip(args).foldLeft(env)((en, xv) => en.bind(xv._1, xv._2))))

  /** A constant as Scala holds it, and a Scala value as a constant: both by its type. */
  def literal(v: Value, t: Ty): ScalaValue = literals(v, t)
  def reflect(v: ScalaValue, t: Ty): Value = reflected(v, t)

  private def of(f: Form): Env => Either[EvalError, ScalaValue] = f match
    case Form.Term(s)  => term(s)
    case Form.Steps(_) => _ => Left(EvalError.Steps)
