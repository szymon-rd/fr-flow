package frflow.proof.prover.ast

/** A binder of a `fun`, a quantifier or a declaration: explicit `(x : T)` (or several of one type, `(A B : Type)`),
  * implicit `{m : T}`, an instance `[Monad m]`, a bare name `x` (`fun w => …`), a bare name whose type is known
  * (`Of`: written as the bare name in the notation a node's content is in, with its type in Rocq, which does not find
  * it from a list given after the function), a membership `x ∈ xs`.
  */
enum LBinder:
  case Explicit(name: ProverName, ty: LExpr)
  case Several(names: List[ProverName], ty: LExpr)
  case Implicit(name: ProverName, ty: LExpr)
  case Instance(cls: LExpr)
  case Bare(name: ProverName)
  case Of(name: ProverName, ty: LExpr)
  case Member(name: ProverName, in: LExpr)
