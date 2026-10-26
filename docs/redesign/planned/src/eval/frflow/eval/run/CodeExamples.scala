package frflow.eval.run

import frflow.core.code.Impl
import frflow.core.example.{CallExample, Given, Verdict}
import frflow.dsl.term.Values
import frflow.eval.{Denote, Fn, ScalaValue}
import scala.util.Try

/** An operation's attached code run on its call examples (today's `checkExamples` on code): built once per set of
  * givens, as a running system builds it, called through `Fn` under the example's values, and its result judged
  * against the example's and the invariants the contract keeps.
  */
final class CodeExamples(denote: Denote, givens: Givens, check: CallCheck, code: Impl):
  def of(examples: List[CallExample]): List[Agreement] =
    examples.foldLeft((Map.empty[List[Given], Try[AnyRef]], Vector.empty[Agreement])) { case ((built, out), e) =>
      val f = built.getOrElse(e.givens, Values.within(givens.values(e.givens))(Try(code.make())))
      (built.updated(e.givens, f), out :+ run(f, e))
    }._2.toList

  private def run(f: Try[AnyRef], e: CallExample): Agreement = Values.within(givens.values(e.givens)) {
    val inputs = e.inputs.zip(check.inputs).map(denote.literal)
    f.flatMap(g => Try(Fn.call(g, inputs)))
      .fold(t => Agreement.Breaks(Broken.Threw(String.valueOf(t.getMessage))), got => judged(e, inputs :+ got))
  }

  /** An invariant broken, or the result against the example's (an `expect` must return it, a `reject` must not). */
  private def judged(e: CallExample, call: List[ScalaValue]): Agreement =
    val value = denote.reflect(call.last, check.result)
    check.kept.iterator.flatMap(_.broken(call, givens.env(e.givens))).nextOption() match
      case Some(b)                                                      => Agreement.Breaks(b)
      case None if (value == e.result) == (e.verdict == Verdict.Expect) => Agreement.Agrees
      case None                                                         => Agreement.Returned(value)
