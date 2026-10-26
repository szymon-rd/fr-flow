package frflow.core.spec

import frflow.core.expr.{Expr, Lambda}

/** What every call (or run) of an operation meets: the post, the cheaper check run time uses when given, and the
  * examples, each of the call's shape `E`.
  */
final case class Promise[E](post: Written[Lambda], check: Option[Written[Lambda]], examples: List[E]):
  def exprs: List[Expr] = post.value.body :: check.toList.map(_.value.body)
  def withExamples(more: List[E]): Promise[E] = copy(examples = examples ++ more)
