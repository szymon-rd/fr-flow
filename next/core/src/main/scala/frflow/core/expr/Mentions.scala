package frflow.core.expr

import cats.kernel.Monoid
import frflow.core.name.{DefName, ModelName, SymbolName, TypeName}

/** What an expression mentions, each name once, in the order first met: a monoid on values whose lists hold no name
  * twice (as every one `Exprs.mentions` gives does): the symbols named as values, the defines called, the types,
  * the operations on a state a program's steps call, and the models whose state is read or written. The analyses
  * read this, never Lean text.
  */
final case class Mentions(symbols: List[SymbolName], defines: List[DefName], types: List[TypeName],
    operations: List[SymbolName], models: List[ModelName])

object Mentions:
  val empty: Mentions = Mentions(Nil, Nil, Nil, Nil, Nil)
  given Monoid[Mentions] = Monoid.instance(empty, (a, b) =>
    Mentions((a.symbols ++ b.symbols).distinct, (a.defines ++ b.defines).distinct, (a.types ++ b.types).distinct,
      (a.operations ++ b.operations).distinct, (a.models ++ b.models).distinct))
