package rooms

import frflow.core.expr.{Expr, Lambda}
import frflow.core.spec.{CallForm, Statement, Written}
import frflow.dsl.build.Deferred
import frflow.dsl.vocab.Definition

/** A model's parts as the analyses read them, each elaborated first: a define's written lambda, the call a statement
  * reads as, and its post. (Their Lean is `next-proof`'s.)
  */
object RoomsIr:
  def elaborated[A](d: Deferred[A]): A = d.run.fold(e => throw AssertionError(e.toString), _._2)

  /** A define's written lambda: what the Definition `define` made carries. */
  def lambda(d: Definition[?]): Written[Lambda] =
    elaborated(d.onTheSpot.fold(throw AssertionError(s"${d.name.value} is not a define"))(_.lambda))

  /** The call (or run) a statement reads as. */
  def call(s: Deferred[Statement]): CallForm = elaborated(s).call.getOrElse(throw AssertionError("reads as no call"))
  def post(s: Deferred[Statement]): Written[Lambda] = call(s).posted

  /** A statement's formula, as the analyses read it. */
  def formula(s: Deferred[Statement]): Expr = elaborated(s) match
    case Statement.Claim(f, _)   => f.value
    case Statement.Assumption(f) => f.value
    case Statement.Design(_)     => throw AssertionError("a design has no formula")
