package frflow.eval.run

import frflow.core.example.{CallExample, Verdict}
import frflow.eval.{Denote, Env, Fn, ScalaValue}

/** An operation's call examples against its promise (today's `checkExamples` on the contract): a fact the example's
  * givens break, else the post's answer against the example's verdict, and an expected call checked against the
  * invariants the contract keeps.
  */
final class PromiseExamples(denote: Denote, givens: Givens, facts: List[Assumes], check: CallCheck):
  def of(examples: List[CallExample]): List[Agreement] = examples.map(e => run(e, givens.env(e.givens)))

  private def run(e: CallExample, env: Env): Agreement =
    val bound = e.givens.map(_.symbol).toSet
    facts.find(f => f.within(bound) && !f.holds(env))
      .fold(answer(e, env, call(e)))(f => Agreement.Breaks(Broken.Assumption(f.id)))

  private def call(e: CallExample): List[ScalaValue] =
    (e.inputs :+ e.result).zip(check.inputs :+ check.result).map(denote.literal)

  private def answer(e: CallExample, env: Env, call: List[ScalaValue]): Agreement = check.post.run(env, call) match
    case Left(err)                                             => Agreement.Breaks(Broken.NotEvaluated(err))
    case Right(v) if Fn.bool(v) && e.verdict == Verdict.Expect => kept(call, env)
    case Right(v)                                              => Agreement.judged(Fn.bool(v), e.verdict)

  /** An expected call the promise accepts still breaks an invariant the contract keeps. */
  private def kept(call: List[ScalaValue], env: Env): Agreement =
    check.kept.iterator.flatMap(_.broken(call, env)).nextOption().fold(Agreement.Agrees)(Agreement.Breaks(_))
