package frflow.dsl.vocab

import frflow.core.term.Sym
import frflow.dsl.term.{LeanType, Term, Terms}

/** A Definition passed where a list's operation takes a function of its elements (`held.pairwise(apart)`,
  * `xs.forall(endsAfterStart)`): applied to each, its binders named as Lean's `fun a b`.
  */
object DefinitionSyntax:
  extension [A: LeanType](xs: Term[List[A]])
    def pairwise(d: Definition[(A, A) => Boolean]): Term[Boolean] = Terms.pairwise(xs, ("a", "b"))((a, b) => d(a, b))
    def forall(d: Definition[A => Boolean]): Term[Boolean] =
      Terms.over(xs, "x", (a: Term[A]) => d(a))([T[_]] => (s: Sym[T]) => s.all[A])
