package frflow.proof.lean.ast

/** One line of a `do` block, with what it holds below it: `let x ← s`, `let x := v`, a step, `let x ← do` with a block,
  * a `for` loop, an `if`, a `tryCatchThe`, and `xs.mapM` / `foldlM` with their bodies.
  */
enum DoLine:
  case Bind(name: LeanName, step: LExpr)
  case Let(name: LeanName, value: LExpr)
  case Step(step: LExpr)
  case BindBlock(name: Option[LeanName], body: List[DoLine])
  case For(x: LeanName, over: LExpr, body: List[DoLine])
  case Branch(cond: LExpr, ifTrue: List[DoLine], ifFalse: List[DoLine])
  case TryCatch(lead: Option[LeanName], error: LExpr, body: List[DoLine], x: Option[LeanName], handler: List[DoLine])
  case Traverse(lead: Option[LeanName], head: LExpr, params: List[LeanName], body: List[DoLine])
