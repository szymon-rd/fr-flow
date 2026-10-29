package frflow.dsl.flow

import frflow.core.vocab.Fails
import frflow.dsl.term.{LeanType, Term}

/** How a running program's terms meet plain values (`eval.Running` gives it): a term's value, a value's term, and a
  * failing model's declared error, as the program's handler of that error is given it, for its operations' Scala's
  * failure (`cause`).
  */
trait Terms:
  def value[A](t: Term[A]): A
  def term[A: LeanType](a: A): Term[A]
  def fail(fails: Fails, cause: Throwable): Throwable
