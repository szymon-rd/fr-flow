package frflow.proof.prover.term

import frflow.proof.prover.ast.*
import frflow.proof.prover.ast.Tree.into

/** The text of the tree in the notation a node's content is signed in: the tree read by `Notation`. */
object Print:
  def expr(e: LExpr): String = e.into(Notation)
  def binder(b: LBinder): String = Notation.binder(b.map(expr))
  def binders(bs: List[LBinder]): String = bs.map(binder).mkString(" ")
  private[prover] def params(bs: List[LBinder]): String = bs.map(" " + binder(_)).mkString

  private[prover] def dotted(ns: List[ProverName]): String = ns.map(_.text).mkString(".")
