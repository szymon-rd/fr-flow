package frflow.runtime

import frflow.core.code.Impl
import frflow.core.name.SymbolName
import frflow.dsl.term.Values
import frflow.eval.{Fn, ScalaValue}
import frflow.eval.run.Broken
import frflow.runtime.check.CallValues

/** A contract's code as a running system calls it (today's `enforce`): built and run under the call's own values,
  * then checked by its `Guard`; a broken check reported, then thrown, so a result that breaks the contract is never
  * returned.
  */
final class Service(guard: Guard, code: Impl, values: Map[SymbolName, () => Any], reporter: Reporter):
  /** The service as the developer's typed function. */
  def as[F]: F = Fn.of[F](code.arity)(call)

  def call(inputs: List[ScalaValue]): ScalaValue =
    val now = CallValues(values)
    Values.within(now.inForce) {
      val result = Fn.call(code.make(), inputs)
      guard.result(inputs :+ result).foreach(fail(_, inputs, Some(result)))
      guard.values(now).foreach(fail(_, inputs, None))
      result
    }

  private def fail(b: Broken, inputs: List[ScalaValue], result: Option[ScalaValue]): Nothing =
    val v = Violation(guard.contract, b, inputs, result)
    reporter.report(v)
    throw ContractViolation(v)
