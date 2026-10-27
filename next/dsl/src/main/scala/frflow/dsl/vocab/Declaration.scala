package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.vocab.ValueKind
import frflow.dsl.build.Source
import frflow.dsl.term.{LeanType, Term}
import scala.annotation.publicInBinary

/** An abstract value (owner §15), of any type, named as its val (`val authorized = Declaration[(UserId, Path) =>
  * Boolean]("whether …")`): known only through the statements about it, never called by code or a program, never
  * implemented. It is not a term: it is applied only where a statement is being written (`Stating`), so code that
  * names it does not compile. Consistency asks a witness for it, usually from what refines it.
  */
final class Declaration[A] @publicInBinary private (val name: SymbolName, val means: String)(
    using val leanType: LeanType[A]):
  /** The value as a term, in a statement. */
  def term(using Stating): Term[A] = Term(Symbols.term[A](name, means, ValueKind.Declaration, leanType))
  private def curried[F: LeanType]: Term[F] = Term(Symbols.term[F](name, means, ValueKind.Declaration, leanType))

object Declaration:
  inline def apply[A: LeanType](means: String): Declaration[A] = new Declaration[A](SymbolName(Source.valName), means)

  extension [A, R](d: Declaration[A => R])
    def apply(a: Term[A])(using Stating, LeanType[R]): Term[R] = Term.app(d.curried[A => R](using d.leanType), a)
  extension [A, B, R](d: Declaration[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using Stating, LeanType[A], LeanType[B], LeanType[R]): Term[R] =
      Term.app(Term.app(d.curried[A => B => R], a), b)
  extension [A, B, C, R](d: Declaration[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using Stating, LeanType[A], LeanType[B], LeanType[C], LeanType[R])
        : Term[R] = Term.app(Term.app(Term.app(d.curried[A => B => C => R], a), b), c)
  extension [A, B, C, D, R](d: Declaration[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(
        using Stating, LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[R]): Term[R] =
      Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => R], a), b), c), e)
  extension [A, B, C, D, E, R](d: Declaration[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E])(
        using Stating, LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[E], LeanType[R]): Term[R] =
      Term.app(Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => E => R], a), b), c), e), f)
  extension [A, B, C, D, E, G, R](d: Declaration[(A, B, C, D, E, G) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[G])(using Stating, LeanType[A],
        LeanType[B], LeanType[C], LeanType[D], LeanType[E], LeanType[G], LeanType[R]): Term[R] =
      Term.app(Term.app(Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => E => G => R], a), b), c), e),
        f), g)
