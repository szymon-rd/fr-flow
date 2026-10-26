package frflow.runtime.check

import frflow.core.name.SymbolName
import frflow.dsl.term.Once

/** One call's values: each read when first needed, then the same for the rest of the call, so the code and its
  * checks see the same values and a table nothing reads is never loaded. Made for each call and dropped after it.
  */
final class CallValues(bound: Map[SymbolName, () => Any]):
  private val cells: Map[SymbolName, Once[Any]] = bound.map((s, _) => s -> Once[Any]())

  /** The values in force for the call (`Values.within`). */
  val inForce: Map[SymbolName, () => Any] = bound.map((s, read) => s -> (() => cells(s).get(read())))

  def loaded(s: SymbolName): Boolean = cells.get(s).exists(_.held.nonEmpty)
  def value(s: SymbolName): Option[Any] = inForce.get(s).map(_())
