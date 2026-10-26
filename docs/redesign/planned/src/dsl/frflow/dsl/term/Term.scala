package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr}
import frflow.dsl.build.Declarations

/** A value of the domain as a model writes it: an expression of the IR typed by Scala as `A`, with its notes. Built
  * only while a knowledge base is elaborated; `==` on terms does not compile, `===` says the values are equal.
  */
open class Term[A](val expr: Expr, val notes: Notes)(using val leanType: LeanType[A])

object Term:
  /** An operation's result: its notes are its operands' and its own type's. */
  def of[A](e: Expr, operands: Term[?]*)(using t: LeanType[A]): Term[A] =
    Term(e, operands.toList.foldMap(_.notes) |+| Notes.of(t.declares))
  def variable(x: Binder): Term[Any] = Term(Expr.Var(x), Notes.of(Declarations.none))(using LeanType.of(x.ty))
