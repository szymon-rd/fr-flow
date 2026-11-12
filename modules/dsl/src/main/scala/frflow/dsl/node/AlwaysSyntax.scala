package frflow.dsl.node

import frflow.dsl.build.Source
import frflow.dsl.shape.Defines
import frflow.dsl.term.{LeanType, Term, Terms}
import frflow.dsl.vocab.Definition

/** `always`, beside `forall` (every possible value): `always[T](x => …)`, every value of `T` that can be made. The
  * rule is a define named as the node's val, so the prover names it in every hypothesis it becomes.
  */
object AlwaysSyntax:
  inline def always[A: LeanType](inline rule: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.always[A](Source.of(rule).params.headOption.getOrElse("x"), applied(Defines.define(rule)))

  /** The rule as the function `Terms.always` binds: its define applied to the bound value. */
  def applied[A](rule: Definition[A => Boolean]): Term[A] => Term[Boolean] = x => rule(x)
