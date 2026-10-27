package frflow
package lean
package obligation

/** What a statement's shape gives: the answer an equation fixes, the condition a claim is stated under. */
object Equations:
  /** The inputs and `e` of a post `guard implies result === e` or `result === e`, `e` not mentioning the result: an
    * answer the statement allows, for every input.
    */
  def answerOf(post: Lifted[?]): Option[(List[Binder], Tree)] =
    val (bs, body) = (post.built._1, post.built._2.termTree)
    bs.lastOption.flatMap { result =>
      def eq(t: Tree): Option[Tree] = t match
        case Tree.Op(Prim.Eq, List(Tree.Var(r), e)) if (r eq result) && !mentions(e, result) => Some(e)
        case Tree.Op(Prim.Eq, List(e, Tree.Var(r))) if (r eq result) && !mentions(e, result) => Some(e)
        case _                                                                               => None
      (body match
        case Tree.Op(Prim.Implies, List(_, conclusion)) => eq(conclusion)
        case other                                      => eq(other)
      ).map(bs.init -> _)
    }

  /** The variables of a claim `forall(xs => p(xs) === e)` (or `e === p(xs)`), and `e`, not mentioning `p`: what `p`
    * is, for every input, said by a claim on no one operation (`p` is not the only one applied to `xs`).
    */
  def definingOf(formula: Lifted[?], p: String): Option[(List[Binder], Tree)] = formula.built._2.termTree match
    case Tree.Quant(true, bs, Tree.Op(Prim.Eq, List(l, r))) =>
      def on(t: Tree) = t match
        case Tree.Apply(Tree.Ref(q), args) => q.name == p && args.map { case Tree.Var(b) => Some(b); case _ => None } ==
          bs.map(Some(_))
        case _                              => false
      if on(l) && !names(r, p) then Some(bs -> r) else if on(r) && !names(l, p) then Some(bs -> l) else None
    case _ => None

  /** The type of what a function-typed term returns. */
  def returnType(p: Param[?]): frflow.types.LeanType[?] = p.termType.shape match
    case frflow.types.Shape.FnOf(_, r) => r
    case _                             => frflow.types.LeanType.unknown

  private def names(t: Tree, p: String): Boolean = t match
    case Tree.Ref(q) => q.name == p
    case _           => Trees.children(t).exists(names(_, p))

  /** The variables of a claim `forall(xs => a implies b)`, and `a`. */
  def conditionOf(formula: Lifted[?]): Option[(List[Binder], Tree)] = formula.built._2.termTree match
    case Tree.Quant(true, bs, Tree.Op(Prim.Implies, List(a, _))) => Some((bs, a))
    case _                                                       => None

  /** The type of what a statement's operation returns. */
  def resultType(n: Node[?]): frflow.types.LeanType[?] = n.op.map(_.termType.shape) match
    case Some(frflow.types.Shape.FnOf(_, r)) => r
    case _                                   => frflow.types.LeanType.unknown

  private def mentions(t: Tree, b: Binder): Boolean = t match
    case Tree.Var(x) => x eq b
    case _           => Trees.children(t).exists(mentions(_, b))
