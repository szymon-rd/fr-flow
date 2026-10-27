package frflow.dsl.vocab

import cats.syntax.all.*
import frflow.core.name.SymbolName
import frflow.core.term.{Final, Sym}
import frflow.core.vocab.{Symbol, SymbolType, ValueKind}
import frflow.dsl.build.Declarations
import frflow.dsl.term.{LeanType, Notes}

/** A named value as a term: the symbol, noting its declaration (its kind, meaning and type) for the vocabulary. */
private[vocab] object Symbols:
  def term[A](name: SymbolName, means: String, kind: ValueKind, declared: LeanType[?]): Final[A] =
    [T[_]] => (s: Sym[T]) => s.noted(Notes.of(declared.declares |+| declares(name, means, kind, declared)),
      s.param[A](name, declared.ty))

  private def declares(name: SymbolName, means: String, kind: ValueKind, t: LeanType[?]): Declarations =
    Declarations.symbol(Symbol(name, means, SymbolType.Typed(t.ty), kind))
