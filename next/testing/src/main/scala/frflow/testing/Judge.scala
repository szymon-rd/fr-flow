package frflow.testing

import frflow.core.code.Impl
import frflow.core.name.NodeId
import frflow.core.spec.CallForms
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.eval.{Applied, Env, Fn, Semantics}
import frflow.eval.run.{Broken, CallCheck, Wiring}
import scala.util.Try

/** What one generated case of a node's code is judged by: the types of its inputs, and what a case breaks. A claim
  * read as a call of a Definition with plain code judges the call (`CallCheck`: the post, each `always[T]` of the
  * call's values); any other claim is evaluated whole at the case's variables, every Definition given its meaning.
  */
final case class Judge(inputs: List[Ty], broken: Case => Option[Broken])

object Judge:
  def of(semantics: Semantics, t: Theory, node: NodeId): Option[Judge] =
    val wiring = Wiring(semantics, t)
    CallCheck.of(semantics, t, node) match
      case Some(check) => code(t, check).map(impl => Judge(check.inputs, c => call(semantics, wiring)(check, impl, c)))
      case None        => t.node(node).flatMap(_.statement.said).map(CallForms.whole).map { w =>
          val types = w.value.params.map(_.ty)
          Judge(types, c => whole(semantics, wiring)(semantics.lambda(w), types, c))
        }

  /** What one case breaks, if anything: the code's exception, the post, an `always[T]` of a value given or made. */
  def call(semantics: Semantics, wiring: Wiring)(check: CallCheck, code: Impl, c: Case): Option[Broken] =
    val values = wiring.values(wiring.supplied(c.givens))
    val args = c.inputs.zip(check.inputs).map(semantics.literal)
    Try(Fn.call(code.make(values), args))
      .fold(e => Some(Broken.Threw(String.valueOf(e.getMessage))), got => check.broken(args :+ got, Env.of(values)))

  /** A claim read whole, at a case's variables, each Definition given its meaning. */
  private def whole(semantics: Semantics, wiring: Wiring)(claim: Applied, types: List[Ty], c: Case): Option[Broken] =
    val env = Env.of(wiring.values(wiring.supplied(c.givens)))
    Try(claim.run(env, c.inputs.zip(types).map(semantics.literal))).fold(
      e => Some(Broken.Threw(String.valueOf(e.getMessage))), {
        case Left(e)                 => Some(Broken.NotEvaluated(e))
        case Right(v) if !Fn.bool(v) => Some(Broken.Post)
        case Right(_)                => None
      })

  private def code(t: Theory, check: CallCheck): Option[Impl] =
    t.code.attached.get(check.op).flatMap(_.code.scala).map(_.impl)
