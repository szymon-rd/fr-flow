package frflow.core.code

import frflow.core.name.SymbolName

/** The values plain code is given, passed to it explicitly (`implement(c)(env => …)`): each symbol's value, computed
  * when read. Whoever runs the code makes them (`eval.run.Wiring`); `dsl`'s `env(p)` reads one, typed by its
  * declaration (`Open`, `Operation`).
  */
final case class Values(read: Map[SymbolName, () => Any]):
  def get(s: SymbolName): Option[Any] = read.get(s).map(_())
  def ++(more: Values): Values = Values(read ++ more.read)

object Values:
  val none: Values = Values(Map.empty)
