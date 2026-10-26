package frflow.dsl.term

import frflow.core.name.SymbolName

/** The values in force where plain code runs, read by `Param.value`: set for one call by whatever runs the code. */
object Values:
  private val scope: ThreadLocal[Map[SymbolName, () => Any]] = ThreadLocal.withInitial(() => Map.empty)

  def read(s: SymbolName): Option[Any] = scope.get.get(s).map(_())

  def within[A](values: Map[SymbolName, () => Any])(body: => A): A =
    val outer = scope.get
    scope.set(outer ++ values)
    try body
    finally scope.set(outer)
