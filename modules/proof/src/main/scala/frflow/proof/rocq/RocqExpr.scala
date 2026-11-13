package frflow.proof.rocq

import frflow.proof.prover.ast.{LBinder, LExpr}
import frflow.proof.prover.ast.Tree.into
import frflow.proof.rocq.RocqNames.Scope

/** Rocq's text of a term of the tree: the tree read by `RocqSyntax`. */
private[rocq] final class RocqExpr(names: RocqNames):
  private val syntax = RocqSyntax(names)

  def apply(e: LExpr)(using s: Scope): String = e.into(syntax).text(s)
  def binder(b: LBinder)(using s: Scope): String = syntax.binder(b.map(_.into(syntax)))(s)
  def over(ps: List[LBinder])(using s: Scope): Scope = s.binding(ps.flatMap(_.bound.map(_.text)))

private[rocq] object RocqExpr:
  /** A form of the generated AST Rocq is not printed from yet: a module that holds one is not printed. */
  final class Unsupported(val form: String) extends RuntimeException(s"FrFlow: no Rocq for $form yet")
