package frflow.eval

import cats.syntax.all.*
import frflow.core.expr.PrimOp

/** The operators' Scala meaning, each as today's `Eval.prim`. */
object DenotePrim:
  private type Run = Env => Either[EvalError, ScalaValue]

  def apply(op: PrimOp, args: List[Run]): Run = (op, args) match
    case (PrimOp.And, List(a, b)) => env => a(env).flatMap(x => if Fn.bool(x) then b(env) else Right(x))
    case (PrimOp.Eq, List(a, b))  => env => (a(env), b(env)).mapN((x, y) => ScalaValue(x.unwrap == y.unwrap))
    case _                        => ??? // the other operators, one line each
