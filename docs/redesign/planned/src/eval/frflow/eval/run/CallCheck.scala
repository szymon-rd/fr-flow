package frflow.eval.run

import frflow.core.name.NodeId
import frflow.core.spec.{Promise, Statement}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.eval.{Applied, Denote, Env, Fn, ScalaValue}

/** What one call of an operation is checked against, compiled once: its post (examples), its check (where it runs:
  * the cheaper one when given, else the post) and the invariants its contract keeps, each through its view. A call
  * is its inputs, then its result.
  */
final case class CallCheck(post: Applied, which: Broken, check: Applied, kept: List[Kept], inputs: List[Ty],
    result: Ty):
  def broken(call: List[ScalaValue], env: Env): Option[Broken] = check.run(env, call) match
    case Left(e)                 => Some(Broken.NotEvaluated(e))
    case Right(v) if !Fn.bool(v) => Some(which)
    case Right(_)                => kept.iterator.flatMap(_.broken(call, env)).nextOption()

object CallCheck:
  /** A contract's, or an assumption's about an operation (its adapter is checked on its examples). */
  def of(denote: Denote, t: Theory, node: NodeId): Option[CallCheck] = t.node(node).map(_.statement).collect {
    case Statement.Contract(_, p, _) => from(denote, p, Kept.of(denote, t, node))
    case Statement.AssumedCall(_, p) => from(denote, p, Nil)
  }

  private def from(denote: Denote, p: Promise[?], kept: List[Kept]): CallCheck =
    val types = p.post.value.params.map(_.ty)
    val (which, l) = p.check.fold((Broken.Post, p.post.value))(c => (Broken.Check, c.value))
    CallCheck(denote.lambda(p.post.value), which, denote.lambda(l), kept, types.init, types.last)
