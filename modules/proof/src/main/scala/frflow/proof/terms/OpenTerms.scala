package frflow.proof.terms

import cats.kernel.Monoid
import frflow.core.name.{SymbolName, TypeName}

/** The open terms a statement is over, in order: its binders in Lean (opaque types first, then symbols). A monoid:
  * the union keeping first occurrences, so the binders of a composed statement are those of its parts in order.
  */
final case class OpenTerms(sorts: List[TypeName], symbols: List[SymbolName])

object OpenTerms:
  val empty: OpenTerms = OpenTerms(Nil, Nil)
  given Monoid[OpenTerms] =
    Monoid.instance(empty, (a, b) => OpenTerms((a.sorts ++ b.sorts).distinct, (a.symbols ++ b.symbols).distinct))
