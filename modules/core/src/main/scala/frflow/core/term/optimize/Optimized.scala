package frflow.core.term.optimize

import frflow.core.term.language.Final

/** The optimizations of code, as a chain: each pass an interpreter over the term with the little it needs to know
  * of it, `fwd` into that and `bwd` out (`interpret.Forward`; Kiselyov, "Modular, composable, typed optimizations
  * in the tagless-final style"). A pass interprets only the operations it changes; every other goes through as it
  * is, so a pass knows nothing of the rest of the language, or of the other passes. What one pass writes the next
  * reads at once, and a pass is run again where another opens what it takes: a `let` that named a pair, once
  * read as the pair, has its parts read by `Projected` after it.
  *
  * What they take out is what the code compiled from a class is full of: the result and the state a member gives
  * are a pair, taken apart where the next step begins; a step's traces start as lists with no member.
  */
object Optimized:
  def of[A](t: Final[A]): Final[A] = Projected.of(Inlined.of(Joined.of(Decided.of(Projected.of(t)))))
