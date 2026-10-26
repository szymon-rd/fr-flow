package frflow.eval.run

import frflow.core.example.{Given, Supply}
import frflow.core.expr.Value
import frflow.core.name.SymbolName
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Denote, Env, ScalaValue}

/** The values an example runs under, from its givens: values in force for its plain code (`Values.within`), and the
  * symbols of an `Env` for the IR. Data and tables are literals of the symbol's type; code is run when read.
  */
final class Givens(denote: Denote, typeOf: SymbolName => Option[Ty]):
  def values(gs: List[Given]): Map[SymbolName, () => Any] = gs.map(g => g.symbol -> value(g)).toMap

  def env(gs: List[Given]): Env =
    val vs = values(gs)
    Env(Map.empty, s => vs.get(s).map(read => ScalaValue(read())), 0)

  private def value(g: Given): () => Any = g.supply match
    case Supply.Data(v)    => constant(v, g.symbol)
    case Supply.Table(es)  => constant(Value.Pairs(es), g.symbol)
    case Supply.Code(impl) => () => impl.make()

  /** `Validate` refuses data for a symbol with no type (`DataForCodeOnly`). */
  private def constant(v: Value, s: SymbolName): () => Any =
    val ty = typeOf(s).getOrElse(throw IllegalStateException(s"FrFlow bug: data given for ${s.value}, of no type"))
    val held = denote.literal(v, ty).unwrap
    () => held

object Givens:
  /** Over a theory: each symbol's type from its vocabulary (a symbol only plain code reads has none). */
  def of(denote: Denote, t: Theory): Givens = Givens(denote, s =>
    t.vocabulary.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) => ty })
