package frflow.eval.term

import frflow.core.code.Values
import frflow.dsl.term.LeanType
import frflow.dsl.vocab.Definition
import frflow.eval.{Env, NotEvaluated}

/** `d.fn(env)` in plain code: a Definition as a Scala function over the values it is given; a define's body run by
  * the evaluator (`Evaluate`) on the arguments, nothing compiled or cached.
  */
object DefSyntax:
  extension [A, R](d: Definition[A => R])
    def fn(env: Values): A => R =
      a => run(Evaluate.app(d.curried[A => R](using d.leanType).run[Run](Evaluate), Run.pure(a)), env)
  extension [A, B, R](d: Definition[(A, B) => R])
    def fn(env: Values)(using LeanType[A], LeanType[B], LeanType[R]): (A, B) => R = (a, b) =>
      run(Evaluate.app(Evaluate.app(d.curried[A => B => R].run[Run](Evaluate), Run.pure(a)), Run.pure(b)), env)
  // … for 0 to 6 inputs.

  private def run[R](r: Run[R], env: Values): R = r(Env.of(env)).fold(e => throw NotEvaluated(e), identity)
