package frflow
package node

/** A contract written as a claim, `forall((a, b) => … op(a, b) …)`: its post is the formula's body with each `op(a, b)`
  * read as the call's result, over the forall's variables and then the result.
  */
private[frflow] object ClaimShaped:
  def post(op: Param[?], formula: Lifted[?]): Lifted[Nothing] =
    Lifted(() => over(op, formula.built._2.termTree), null, formula.source)

  private def over(op: Param[?], formula: Tree): (List[Binder], Term[?]) =
    val (bs, body) = formula match
      case Tree.Quant(true, bs, body) => (bs, body)
      case other                      => (Nil, other)
    val result = Binder("result", Node.lambdaTypes(op).last)
    (bs :+ result, Term(read(op, body, Tree.Var(result)), summon[LeanType[Boolean]]))

  /** `t` with each call of `op` replaced by `result`, one at a time: a replacement rebuilds the trees around it. */
  @scala.annotation.tailrec
  private def read(op: Param[?], t: Tree, result: Tree): Tree = call(op, t) match
    case Some(c) => read(op, Trees.replace(t, c, result), result)
    case None    => t

  private def call(op: Param[?], t: Tree): Option[Tree] = t match
    case Tree.Apply(Tree.Ref(p), _) if p eq op => Some(t)
    case _                                     => Trees.children(t).iterator.flatMap(call(op, _)).nextOption()
