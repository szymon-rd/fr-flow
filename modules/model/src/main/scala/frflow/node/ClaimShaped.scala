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
    val bool = summon[LeanType[Boolean]]
    if isFlow(op) && bs.nonEmpty then
      // A run from the forall's last variable, the world before: its answer and the world after are the call's.
      val types = Node.lambdaTypes(op)
      val (result, after) = (Binder("result", types(types.size - 3)), Binder("after", types.last))
      val read = runs(op, body, Map(1 -> Tree.Var(result), 2 -> Tree.Var(after)))
      (bs.init ++ List(result, bs.last, after), Term(read, bool))
    else
      val result = Binder("result", Node.lambdaTypes(op).last)
      (bs :+ result, Term(read(op, body, Tree.Var(result)), bool))

  private def isFlow(op: Param[?]): Boolean = op.termType.shape match
    case frflow.types.Shape.FnOf(_, r) => r.shape.isInstanceOf[frflow.types.Shape.FlowOf]
    case _                             => false

  /** `t` with each run of `op` (`op(a).answer(w)`, `op(a).after(w)`) replaced by its answer or its world after. */
  @scala.annotation.tailrec
  private def runs(op: Param[?], t: Tree, by: Map[Int, Tree]): Tree = run(op, t) match
    case Some(r @ Tree.Proj(_, k, _)) => runs(op, Trees.replace(t, r, by(k)), by)
    case _                            => t

  private def run(op: Param[?], t: Tree): Option[Tree] = t match
    case Tree.Proj(Tree.RunOn(Tree.Apply(Tree.Ref(p), _), _, _), k, 2) if (p eq op) && (k == 1 || k == 2) => Some(t)
    case _ => Trees.children(t).iterator.flatMap(run(op, _)).nextOption()

  /** `t` with each call of `op` replaced by `result`, one at a time: a replacement rebuilds the trees around it. */
  @scala.annotation.tailrec
  private def read(op: Param[?], t: Tree, result: Tree): Tree = call(op, t) match
    case Some(c) => read(op, Trees.replace(t, c, result), result)
    case None    => t

  private def call(op: Param[?], t: Tree): Option[Tree] = t match
    case Tree.Apply(Tree.Ref(p), _) if p eq op => Some(t)
    case _                                     => Trees.children(t).iterator.flatMap(call(op, _)).nextOption()
