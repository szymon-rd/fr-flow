package frflow.proof.lean.ast

/** A binder of a `fun`, a quantifier or a declaration: explicit `(x : T)` (or several of one type, `(A B : Type)`),
  * implicit `{m : T}`, an instance `[Monad m]`, a bare name `x` (`fun w => …`), a membership `x ∈ xs`.
  */
enum LBinder:
  case Explicit(name: LeanName, ty: LExpr)
  case Several(names: List[LeanName], ty: LExpr)
  case Implicit(name: LeanName, ty: LExpr)
  case Instance(cls: LExpr)
  case Bare(name: LeanName)
  case Member(name: LeanName, in: LExpr)
