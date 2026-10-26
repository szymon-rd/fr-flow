package frflow.proof.lean.lower

import frflow.proof.lean.ast.{LExpr, Names}

/** The Lean the lowering spells itself: a name (`some`, `pure`, `Int`) and a dotted constant (`List.filter`). */
object Atoms:
  def name(s: String): LExpr = LExpr.Name(Names.builtin(s))
  def const(dotted: String): LExpr = LExpr.Const(dotted.split('.').toList.map(Names.builtin))
  /** `(f a b)`: an application in parentheses, as every call is generated. */
  def call(f: LExpr, args: List[LExpr]): LExpr = LExpr.Paren(LExpr.App(f, args))
