package frflow.core.expr

import frflow.core.name.{CtorName, DefName, SymbolName, TypeName}
import frflow.core.ty.Ty

/** An expression of the term language, the initial form of a term (`ToExpr`): a simply typed lambda calculus over
  * the vocabulary. A binder is numbered by its level (`VarId`), so none captures another. */
enum Expr:
  case Var(x: Binder)
  case Lit(value: Value, ty: Ty)
  /** An open term of the vocabulary, or a defined one (applied to its definition by the Lean back end). */
  case Sym(name: SymbolName, ty: Ty)
  case Call(define: DefName, args: List[Expr], ty: Ty)
  case Apply(fn: Expr, args: List[Expr], ty: Ty)
  case Fun(lambda: Lambda)
  case Quant(q: Quantifier, xs: List[Binder], body: Expr)
  case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)
  case Match(on: Expr, arms: List[Arm], ty: Ty)
  case Let(x: Binder, value: Expr, body: Expr)
  case Field(on: Expr, data: TypeName, index: Int, ty: Ty)
  case Copy(on: Expr, data: TypeName, updates: List[(Int, Expr)])
  case Make(data: TypeName, ctor: CtorName, args: List[Expr])
  case Tuple(elems: List[Expr])
  case SomeOf(elem: Expr)
  case Inject(side: Side, elem: Expr, ty: Ty)
  case ListOf(elems: List[Expr], elem: Ty)
  case Iterate(how: Iteration, over: Expr, x: Binder, body: Expr, ty: Ty)
  case Fold(over: Expr, init: Expr, acc: Binder, x: Binder, body: Expr)
  /** `body` of every element with each later one (Lean's `List.Pairwise`). */
  case Pairwise(over: Expr, x: Binder, y: Binder, body: Expr)
  case Prim(op: PrimOp, args: List[Expr], ty: Ty)
