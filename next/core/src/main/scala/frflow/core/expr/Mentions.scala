package frflow.core.expr

import cats.kernel.Monoid
import frflow.core.name.{BoundaryName, DefName, ModelName, SymbolName, TypeName}

/** What an expression mentions, each name once, in the order first met: a monoid on values whose lists hold no name
  * twice (as every one `Exprs.mentions` gives does). The analyses read this, never Lean text.
  */
final case class Mentions(symbols: List[SymbolName], defines: List[DefName], types: List[TypeName],
    boundaries: List[BoundaryName], models: List[ModelName])

object Mentions:
  val empty: Mentions = Mentions(Nil, Nil, Nil, Nil, Nil)
  given Monoid[Mentions] = Monoid.instance(empty, (a, b) =>
    Mentions((a.symbols ++ b.symbols).distinct, (a.defines ++ b.defines).distinct, (a.types ++ b.types).distinct,
      (a.boundaries ++ b.boundaries).distinct, (a.models ++ b.models).distinct))
