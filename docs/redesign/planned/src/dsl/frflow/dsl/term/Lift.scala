package frflow.dsl.term

import frflow.core.expr.{Expr, Value}
import scala.util.NotGiven

/** The DSL's implicit conversions, all of them: a value where a term is expected is the constant (Booleans are
  * written `True` and `False`), an `Int` literal a `BigInt` term. A value that is not data is noted on the term.
  */
object Lift:
  given value[A](using t: LeanType[A], notBoolean: NotGiven[A =:= Boolean]): Conversion[A, Term[A]] = constant(_)
  given int[A <: Int]: Conversion[A, Term[BigInt]] = i => constant(BigInt(i))

  def constant[A](a: A)(using t: LeanType[A]): Term[A] = Reify(t, a) match
    case Right(v) => Term(Expr.Lit(v, t.ty), Notes.of(t.declares))
    case Left(f)  => Term(Expr.Lit(Value.Unit, t.ty), Notes.fault(f)) // never elaborated: the fault fails the node
