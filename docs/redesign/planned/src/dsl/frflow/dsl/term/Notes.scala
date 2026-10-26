package frflow.dsl.term

import cats.data.Chain
import cats.kernel.Monoid
import frflow.dsl.build.{Declarations, Fault}

/** What a term carries besides its expression: the vocabulary it mentions, and the faults found building it (a
  * constant that is not data), placed at the node or define it is in by `Elab`. A monoid: an operation's notes are
  * its operands'.
  */
final case class Notes(declares: Declarations, faults: Chain[Fault])

object Notes:
  def of(d: Declarations): Notes = Notes(d, Chain.empty)
  def fault(f: Fault): Notes = Notes(Declarations.none, Chain.one(f))
  given Monoid[Notes] = Monoid.instance(Notes(Declarations.none, Chain.empty),
    (a, b) => Notes(Monoid[Declarations].combine(a.declares, b.declares), a.faults ++ b.faults))
