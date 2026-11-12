package frflow.core.expr

import cats.kernel.Monoid
import frflow.core.name.{DefName, SymbolName, TypeName}

/** What an expression mentions, each name once, in the order first met: a monoid on values whose lists hold no name
  * twice (as every one `Exprs.mentions` gives does): the symbols named as values, the defines called and the types.
  * The analyses read this, never the prover's text.
  */
final case class Mentions(symbols: List[SymbolName], defines: List[DefName], types: List[TypeName])

object Mentions:
  val empty: Mentions = Mentions(Nil, Nil, Nil)

  given Monoid[Mentions] = Monoid.instance(empty, (a, b) =>
    Mentions((a.symbols ++ b.symbols).distinct, (a.defines ++ b.defines).distinct, (a.types ++ b.types).distinct))
