package frflow.core.spec

import frflow.core.expr.{Expr, Lambda}
import frflow.core.name.SymbolName

/** A formula read as a call of one Definition on its leading variables (`granted(held, request) === …`), or as a
  * run of a program from the world before (`book(request).from(before) { … }`): the post a test checks a call of
  * that Definition's code against, and for a run what a failing run meets. Derived from the formula (`CallForms`),
  * never written.
  */
enum CallForm:
  case Call(op: SymbolName, post: Written[Lambda])
  case Run(op: SymbolName, post: Written[Lambda], failure: Option[FailureClause])

  def definition: SymbolName = this match
    case Call(o, _)   => o
    case Run(o, _, _) => o

  def posted: Written[Lambda] = this match
    case Call(_, p)   => p
    case Run(_, p, _) => p

  def exprs: List[Expr] = this match
    case Call(_, _)      => Nil
    case Run(_, _, fail) => fail.toList.flatMap(_.exprs)
