package frflow.core.expr

import frflow.core.name.{CtorName, DefName, ModelName, SymbolName, TypeName}
import frflow.core.ty.Ty

/** An expression of the term language: a simply typed lambda calculus over the vocabulary. Binders are unique. */
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
  case Proj(on: Expr, index: Int, ty: Ty)
  case SomeOf(elem: Expr)
  case Inject(side: Side, elem: Expr, ty: Ty)
  case ListOf(elems: List[Expr], elem: Ty)
  case Iterate(how: Iteration, over: Expr, x: Binder, body: Expr, ty: Ty)
  case Fold(over: Expr, init: Expr, acc: Binder, x: Binder, body: Expr)
  case Prim(op: PrimOp, args: List[Expr], ty: Ty)
  /** A flow's steps: the body of a `def` over a monad with the boundaries' classes. */
  case Do(prog: Prog, ty: Ty)
  /** A flow (a call of one) run on the models from a world: its result, or outcome, and the world after. */
  case RunOn(call: Expr, world: Expr, failsWith: Option[Ty], ty: Ty)
  /** A model's state in a world. */
  case Part(world: Expr, model: ModelName, ty: Ty)
