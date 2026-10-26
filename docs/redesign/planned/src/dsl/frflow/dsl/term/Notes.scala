package frflow.dsl.term

import cats.data.Chain
import cats.kernel.Monoid
import frflow.core.term.Annotation
import frflow.core.term.interpret.Collect
import frflow.dsl.build.{Declarations, Fault}

/** What a term carries for elaboration besides its meaning: the vocabulary it mentions, and the faults found building
  * it (a constant that is not data), placed at the node or define it is in by `Elab`. Attached to the term where they
  * arise (`noted`), and gathered once by an interpreter (`Collect`), so no operation merges them.
  */
final case class Notes(declares: Declarations, faults: Chain[Fault]) extends Annotation

object Notes:
  def of(d: Declarations): Notes = Notes(d, Chain.empty)
  def fault(f: Fault): Notes = Notes(Declarations.none, Chain.one(f))
  given Monoid[Notes] = Monoid.instance(Notes(Declarations.none, Chain.empty),
    (a, b) => Notes(Monoid[Declarations].combine(a.declares, b.declares), a.faults ++ b.faults))

  /** Every note of a term, gathered. */
  def in(t: Term[?]): Notes = Monoid[Notes].combineAll(Collect.of(t.run).collect { case n: Notes => n })
