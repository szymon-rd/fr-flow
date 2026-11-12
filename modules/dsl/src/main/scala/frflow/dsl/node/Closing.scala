package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Exprs, Quantifier}
import frflow.core.name.VarId
import frflow.dsl.build.Fault
import frflow.dsl.term.{Forall, Term}

/** A statement as its node holds it: its leading `forall`s can be opened (`Forall`), to read what is below them on
  * their variables. Refused where its reading would not be the one written: an `always` inside it
  * (`Fault.AlwaysInside`).
  */
object Closing:
  def of(t: Term[Boolean]): Either[Fault, Term[Boolean]] = Term.exprOf(t).toList.traverse_(alwaysWhole).as(t)

  /** What is below the leading `forall`s, on their variables free: a statement read open, to learn what it reads
    * (the structures it reads as they stand, `Standing`).
    */
  def opened(t: Term[Boolean]): Term[Boolean] = open(t, Nil)._2

  /** The leading `forall`s' bodies on free variables (`VarId.opened`), and what is below them. */
  private def open(t: Term[Boolean], opened: List[(Binder, Forall[?])]): (List[(Binder, Forall[?])], Term[Boolean]) =
    t match
      case f: Forall[a] =>
        val x = Binder(VarId.opened(opened.size), f.hint, f.bound.ty)
        open(f.opened(Term.free[a](x)(using f.bound)), opened :+ (x -> f))
      case body         => (opened, body)

  /** An `always` only as the whole formula: anywhere else it is no rule, and would range over every value. */
  private def alwaysWhole(e: Expr): Either[Fault, Unit] =
    val inside = e match
      case Expr.Quant(Quantifier.Always, _, body) => body
      case other                                  => other
    Either.cond(!Exprs.all(inside).exists {
      case Expr.Quant(Quantifier.Always, _, _) => true
      case _                                   => false
    }, (), Fault.AlwaysInside)
