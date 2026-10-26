package frflow.dsl.term

import frflow.core.expr.{Expr, PrimOp}

/** The operations of the term language, each building one case of `Expr` (a sample: the full set is today's). */
object TermSyntax:
  private def prim[R: LeanType](op: PrimOp, args: Term[?]*): Term[R] =
    Term.of[R](Expr.Prim(op, args.toList.map(_.expr), LeanType[R].ty), args*)

  extension [A](a: Term[A])
    def ===(b: Term[A]): Term[Boolean] = prim(PrimOp.Eq, a, b)
    def =!=(b: Term[A]): Term[Boolean] = prim(PrimOp.Ne, a, b)
  extension (a: Term[Boolean])
    def &&(b: Term[Boolean]): Term[Boolean] = prim(PrimOp.And, a, b)
    def ||(b: Term[Boolean]): Term[Boolean] = prim(PrimOp.Or, a, b)
    def ==>(b: Term[Boolean]): Term[Boolean] = prim(PrimOp.Implies, a, b)
    def unary_! : Term[Boolean] = prim(PrimOp.Not, a)
    def fold[R](ifTrue: Term[R], ifFalse: Term[R]): Term[R] =
      Term.of(Expr.If(a.expr, ifTrue.expr, ifFalse.expr), a, ifTrue, ifFalse)(using ifTrue.leanType)
  extension [A](xs: Term[List[A]])
    def contains(x: Term[A]): Term[Boolean] = prim(PrimOp.Contains, xs, x)
    def length: Term[BigInt] = prim(PrimOp.Length, xs)
