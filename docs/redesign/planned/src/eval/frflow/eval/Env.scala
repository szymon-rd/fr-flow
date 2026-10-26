package frflow.eval

import frflow.core.code.Values
import frflow.core.name.{SymbolName, VarId}

/** What an expression is evaluated under: its variables' values, and the symbols' values it is given. */
final case class Env(variables: Map[VarId, ScalaValue], symbols: SymbolName => Option[ScalaValue]):
  def bind(x: VarId, v: ScalaValue): Env = copy(variables = variables.updated(x, v))
  /** The same, with `s` given `v` (a claim's Definition, as the call's result for its inputs). */
  def withSymbol(s: SymbolName, v: ScalaValue): Env = copy(symbols = n => if n == s then Some(v) else symbols(n))

object Env:
  /** The values given (plain code's, an example's, a test's), and no variables. */
  def of(values: Values): Env = Env(Map.empty, s => values.get(s).map(ScalaValue(_)))
