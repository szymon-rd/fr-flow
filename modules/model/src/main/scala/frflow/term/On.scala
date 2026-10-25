package frflow
package term

import Cases.Fields

/** A further case of a match. */
final class On[S, E <: Tuple, R] @scala.annotation.publicInBinary private[frflow] (scrutinee: Term[S], before: List[Arm], label: String):
  def apply(f: Fields[E, R]): Cases[S, R] = Cases(scrutinee, before :+ Term.namedCase(scrutinee, label, f.asInstanceOf[AnyRef]))
