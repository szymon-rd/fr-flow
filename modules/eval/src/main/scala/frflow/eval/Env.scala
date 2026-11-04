package frflow.eval

import frflow.core.code.Values
import frflow.core.name.{SymbolName, VarId}

/** What an expression is evaluated under: its variables' values, the symbols' values it is given, and the numbers a
  * quantifier over numbers ranges over: none, where it has no Scala value; a search's case's own numbers and their
  * neighbours, where a search only proposes what Lean then proves (the step's refutation).
  */
final case class Env(variables: Map[VarId, ScalaValue], symbols: SymbolName => Option[ScalaValue],
    numbers: List[BigInt]):
  def bind(x: VarId, v: ScalaValue): Env = copy(variables = variables.updated(x, v))
  /** The same, a quantifier over numbers ranging over `ns`. */
  def watching(ns: List[BigInt]): Env = copy(numbers = ns)
  /** The same, with `s` given `v` (a claim's Definition, as the call's result for its inputs). */
  def withSymbol(s: SymbolName, v: ScalaValue): Env = copy(symbols = n => if n == s then Some(v) else symbols(n))

object Env:
  /** The values given (plain code's, an example's, a test's), and no variables. */
  def of(values: Values): Env = Env(Map.empty, s => values.get(s).map(ScalaValue(_)), Nil)
