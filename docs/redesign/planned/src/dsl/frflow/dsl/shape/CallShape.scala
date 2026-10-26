package frflow.dsl.shape

import cats.syntax.all.*
import frflow.core.expr.Lambda
import frflow.core.spec.{Promise, Reliance, Statement, Written}
import frflow.dsl.build.Deferred
import frflow.dsl.term.{LeanType, Param, Term}

/** The shape of a call of an operation of type `F`: the lambdas over a call (its inputs, then its result), their
  * terms' types, and the statement a contract on it makes. One instance per arity and per flow arity. A define's
  * lambda has another shape (`DefineShape`: over its inputs only) and makes no statement.
  */
trait CallShape[F]:
  type Lam[R] <: AnyRef
  type Made <: Statement
  def types: List[LeanType[?]]
  def call[R](f: Lam[R], args: List[Term[Any]]): R
  def contract(op: Param[F], post: Deferred[Written[Lambda]]): Deferred[Made]

object CallShape:
  given two[A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): CallShape[(A, B) => R] with
    type Lam[X] = (Term[A], Term[B], Term[R]) => X
    type Made = Statement.Contract
    val types: List[LeanType[?]] = List(a, b, r)
    def call[X](f: Lam[X], args: List[Term[Any]]): X = args match
      // the binders were made of exactly these types by `Elab.lambda`
      case List(x, y, z) => f(x.asInstanceOf[Term[A]], y.asInstanceOf[Term[B]], z.asInstanceOf[Term[R]])
      case _             => throw IllegalArgumentException("FrFlow bug: a call of arity 2 with other arguments")
    def contract(op: Param[(A, B) => R], post: Deferred[Written[Lambda]]): Deferred[Made] =
      post.map(p => Statement.Contract(op.name, Promise(p, None, Nil), Reliance.Relied))
  // … for 0 to 6 inputs, and for flows (`A => Flow[R]`, `Made = Statement.FlowContract`).
