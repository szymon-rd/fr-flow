package frflow.eval.term

import frflow.core.code.Values
import frflow.dsl.term.RocqType
import frflow.dsl.vocab.Declaration
import frflow.eval.{Env, NotEvaluated}
import frflow.eval.term.Evaluate.app
import frflow.eval.term.Run.pure

/** `d.fn(env)` in plain code: a Definition as a Scala function over the values it is given; a define's body run by
  * the evaluator (`Evaluate`) on the arguments, nothing compiled or cached. A term with no Scala value is thrown as
  * `NotEvaluated`.
  */
object DefSyntax:
  extension [A, R](d: Declaration[A => R])
    def fn(env: Values): A => R = a => run(app(d.curried[A => R](using d.rocqType).run[Run](Evaluate), pure(a)), env)
  extension [A, B, R](d: Declaration[(A, B) => R])
    def fn(env: Values)(using RocqType[A], RocqType[B], RocqType[R]): (A, B) => R = (a, b) =>
      run(app(app(d.curried[A => B => R].run[Run](Evaluate), pure(a)), pure(b)), env)
  extension [A, B, C, R](d: Declaration[(A, B, C) => R])
    def fn(env: Values)(using RocqType[A], RocqType[B], RocqType[C], RocqType[R]): (A, B, C) => R = (a, b, c) =>
      run(app(app(app(d.curried[A => B => C => R].run[Run](Evaluate), pure(a)), pure(b)), pure(c)), env)
  extension [A, B, C, D, R](d: Declaration[(A, B, C, D) => R])
    def fn(env: Values)(using RocqType[A], RocqType[B], RocqType[C], RocqType[D], RocqType[R])
        : (A, B, C, D) => R = (a, b, c, e) =>
      run(app(app(app(app(d.curried[A => B => C => D => R].run[Run](Evaluate), pure(a)), pure(b)), pure(c)), pure(e)),
        env)
  extension [A, B, C, D, E, R](d: Declaration[(A, B, C, D, E) => R])
    def fn(env: Values)(using RocqType[A], RocqType[B], RocqType[C], RocqType[D], RocqType[E], RocqType[R])
        : (A, B, C, D, E) => R = (a, b, c, e, f) =>
      val curried = d.curried[A => B => C => D => E => R].run[Run](Evaluate)
      run(app(app(app(app(app(curried, pure(a)), pure(b)), pure(c)), pure(e)), pure(f)), env)
  extension [A, B, C, D, E, G, R](d: Declaration[(A, B, C, D, E, G) => R])
    def fn(env: Values)(using RocqType[A], RocqType[B], RocqType[C], RocqType[D], RocqType[E], RocqType[G],
        RocqType[R]): (A, B, C, D, E, G) => R = (a, b, c, e, f, g) =>
      val curried = d.curried[A => B => C => D => E => G => R].run[Run](Evaluate)
      run(app(app(app(app(app(app(curried, pure(a)), pure(b)), pure(c)), pure(e)), pure(f)), pure(g)), env)

  private def run[R](r: Run[R], env: Values): R = r(Env.of(env)).fold(e => throw NotEvaluated(e), identity)
