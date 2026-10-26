package frflow.eval

import frflow.core.name.{SymbolName, VarId}
import frflow.dsl.term.Values

/** What an expression is evaluated under: its variables' values, the symbols' values in force, and how many run-time
  * symbols a flow's run has made (`$arg0`, …: the arguments of a call of an implementation, bound by name).
  */
final case class Env(variables: Map[VarId, ScalaValue], symbols: SymbolName => Option[ScalaValue], made: Int):
  def bind(x: VarId, v: ScalaValue): Env = copy(variables = variables.updated(x, v))
  /** A new symbol holding `v`, and the environment where it is bound. */
  def fresh(v: ScalaValue): (SymbolName, Env) =
    val s = SymbolName(s"$$arg$made")
    (s, copy(symbols = n => if n == s then Some(v) else symbols(n), made = made + 1))

object Env:
  /** The symbols in force where plain code runs (`Values`), and no variables. */
  def inForce: Env = Env(Map.empty, s => Values.read(s).map(ScalaValue(_)), 0)
