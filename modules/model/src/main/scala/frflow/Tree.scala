package frflow

import frflow.types.Adt

private[frflow] enum Tree:
  case Var(b: Binder)
  case Lit(v: Any, t: LeanType[?])
  case Ref(p: Param[?])
  case Call(d: Def[?], args: List[Tree])
  case Apply(f: Tree, args: List[Tree])
  case Fun(bs: List[Binder], body: Tree)
  case Quant(all: Boolean, bs: List[Binder], body: Tree)
  case If(c: Tree, a: Tree, b: Tree)
  case Match(on: Tree, cases: List[Arm])
  case Let(b: Binder, v: Tree, body: Tree)
  case Field(on: Tree, adt: Adt, index: Int)
  case Copy(on: Tree, adt: Adt, updates: List[(Int, Tree)])
  case Make(adt: Adt, ctor: frflow.types.Ctor, args: List[Tree])
  case Tup(es: List[Tree])
  case Proj(on: Tree, i: Int, n: Int)
  case SomeT(a: Tree)
  /** An outcome: `Except.error a` (`left`) or `Except.ok a`. */
  case Inj(left: Boolean, a: Tree)
  case ListT(es: List[Tree])
  case Over(kind: Iter, on: Tree, b: Binder, body: Tree)
  case Op(op: Prim, args: List[Tree])
  /** A flow's steps: the body of a `def` over a monad. */
  case Do(steps: Steps)
  /** A flow (a call of one) run on the models from a world: its result and the world after; for a flow that may fail
    * with an error of type `err`, its outcome (`Except E R`) and the world after.
    */
  case RunOn(call: Tree, world: Tree, err: Option[LeanType[?]] = None)
  /** A model's state in a world. */
  case Part(world: Tree, model: StateModel[?])
