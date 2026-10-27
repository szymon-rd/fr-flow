package frflow.dsl.flow

import frflow.dsl.term.{LeanType, Term}

/** How a running program's terms meet plain values (`eval.Running` gives it): a term's value, a value's term. */
trait Terms:
  def value[A](t: Term[A]): A
  def term[A: LeanType](a: A): Term[A]
