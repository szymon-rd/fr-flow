package frflow.eval.run

import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.CallForm
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Applied, Env, EvalError, Fn, ScalaValue, Semantics}

/** What one call of a Definition's plain code is checked against in its generated tests, built once: the post of a
  * claim read as its call (over the call's inputs, the Definition named in it), and the `always[T]`s of the values it
  * is given and makes (its boundary with the code FrFlow covers, owner §16). A call is its inputs, then its result.
  */
final case class CallCheck(post: Applied, op: SymbolName, made: List[Made], inputs: List[Ty], result: Ty):
  /** The post on a call: its inputs bound, the Definition giving the call's result for them. */
  def answer(call: List[ScalaValue], env: Env): Either[EvalError, ScalaValue] =
    post.run(env.withSymbol(op, ScalaValue(Fn.of[AnyRef](inputs.size)(_ => call.last))), call.init)

  def broken(call: List[ScalaValue], env: Env): Option[Broken] = answer(call, env) match
    case Left(e)                 => Some(Broken.NotEvaluated(e))
    case Right(v) if !Fn.bool(v) => Some(Broken.Post)
    case Right(_)                => always(call, env)

  /** An `always[T]` a value of the call breaks: of its inputs and result (or, given only inputs, of those). */
  def always(call: List[ScalaValue], env: Env): Option[Broken] =
    made.iterator.flatMap(_.broken(call, (inputs :+ result).take(call.size), env)).nextOption()

object CallCheck:
  /** Of a statement read as a call, claimed or assumed (an assumption's: its adapter is tested against it). */
  def of(semantics: Semantics, t: Theory, node: NodeId): Option[CallCheck] =
    t.node(node).flatMap(_.statement.call).collect { case CallForm.Call(op, post) =>
      val result = t.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(ty) => Ty.resultOf(ty) }
      CallCheck(semantics.lambda(post), op, Made.of(semantics, t), post.value.params.map(_.ty),
        result.getOrElse(Ty.Unit))
    }
