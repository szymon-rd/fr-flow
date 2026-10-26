package frflow.eval.term

import cats.syntax.all.*
import frflow.eval.{Env, EvalError}

/** A term's value as the evaluator makes it: from the values and variables in scope, or why it has none. */
type Run[A] = Env => Either[EvalError, A]

object Run:
  def pure[A](a: A): Run[A] = _ => Right(a)
  def map2[A, B, C](a: Run[A], b: Run[B])(f: (A, B) => C): Run[C] = env => (a(env), b(env)).mapN(f)
