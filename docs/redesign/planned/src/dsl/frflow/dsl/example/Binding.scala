package frflow.dsl.example

import frflow.core.expr.Value
import frflow.core.name.SymbolName
import frflow.dsl.build.Fault

/** A value an example gives a Definition provided where the code runs (`grants := List(…)`), reified where written. */
final case class Binding(of: SymbolName, value: Either[Fault, Value])
