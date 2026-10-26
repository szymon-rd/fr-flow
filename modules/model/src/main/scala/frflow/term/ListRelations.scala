package frflow
package term

/** What holds of a list's elements taken two at a time: `xs.allDistinct`, `xs.pairwise(apart)`. */
private[frflow] trait ListRelations:
  extension [A](xs: Term[List[A]])
    /** No element occurs twice. Lean's `List.Nodup`. */
    def allDistinct: Term[Boolean] = Term(Tree.Op(Prim.Nodup, List(xs.termTree)), summon[LeanType[Boolean]])
    /** `r` holds of every two elements at different positions, the earlier one first. Lean's `List.Pairwise`; for a
      * symmetric `r`, of every two elements.
      */
    def pairwise(r: (Term[A], Term[A]) => Term[Boolean]): Term[Boolean] =
      val (f, _) = Term.fun(r, List(Term.elem(xs), Term.elem(xs)))
      Term(Tree.Op(Prim.Pairwise, List(f, xs.termTree)), summon[LeanType[Boolean]])
    def pairwise(d: Def[(A, A) => Boolean]): Term[Boolean] = xs.pairwise((a, b) => d(a, b))
