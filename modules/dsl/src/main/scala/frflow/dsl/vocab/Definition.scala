package frflow.dsl.vocab

import cats.syntax.all.*
import frflow.core.name.SymbolName
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType, ValueKind}
import frflow.dsl.build.{Declarations, Source, WrittenAt}
import frflow.dsl.term.{LeanType, Notes, Term}
import scala.annotation.publicInBinary
import scala.compiletime.summonFrom

/** A Declaration with a meaning (owner §15): the word, and what it is. Made of a Declaration already written
  * (`granted.define { … }`, `book.define(bookIfGranted)`, `granted.defineTested(…)`, `limit.defineValue(…)`,
  * `connection.provided`, each listed in the FrModel beside the nodes), or declared and defined at once, named as its
  * val and carrying its proven code (`define { … }`, `lifted { … }`: `onTheSpot`). Every claim mentioning the word
  * constrains it, and its code is checked against them. This class also carries a word that has no meaning yet (what
  * `Declaration[A]("…")` makes, typed as a Declaration): its symbol as a term. Of a type with no `LeanType` (a
  * connection), a word is code-only: provided where the code runs and read there (`env(d)`), never mentioned in a
  * statement (`CodeOnlyInStatement`). `at`: where it is written (`WrittenAt`).
  */
class Definition[A] @publicInBinary private[dsl] (val name: SymbolName, val described: String,
    val onTheSpot: Option[OnTheSpot], val at: WrittenAt)(using t: LeanType[A])
    extends Term[A](Symbols.written(at.declares(name.value), Definition.called[A](name, described, onTheSpot, t)))
    with Declaration[A]:
  def word: Definition[A] = this
  /** The term as a curried function (`F` the curried type of `A`): what `Functions.app` applies. */
  override def curried[F: LeanType]: Term[F] =
    Term(Symbols.written(at.declares(name.value), Definition.called[F](name, described, onTheSpot, t)))
  /** Of a type with no `LeanType`: read only by the code it is provided to. */
  def codeOnly: Boolean = t.codeOnly.nonEmpty
  /** The same Definition, written `at` (`define` says where). */
  private[dsl] def in(at: WrittenAt): Definition[A] = new Definition[A](name, described, onTheSpot, at)
  /** What a code-only Definition declares wherever it is given its meaning: no statement mentions it to. */
  private[dsl] def declares: Declarations =
    t.codeOnly.fold(Declarations.none)(scala =>
      Declarations.symbol(Symbol(name, described, SymbolType.CodeOnly(scala), ValueKind.Definition)) |+|
        at.declares(name.value))

object Definition:
  /** A word named and written as given: of a domain type, or of a type with no `LeanType`, a code-only one, whose
    * term has no type of its own.
    */
  inline def plain[A](name: SymbolName, means: String, at: WrittenAt): Definition[A] = summonFrom {
    case t: LeanType[A] => new Definition[A](name, means, None, at)(using t)
    case _              => new Definition[A](name, means, None, at)(using NoLeanType[A](Source.typeName[A]))
  }

  /** What a code-only Definition is typed by, made only here: no type has it as its given. */
  final class NoLeanType[A] @publicInBinary private[dsl] (scalaType: String) extends LeanType[A]:
    val ty: Ty = Ty.Unit
    val declares: Declarations = Declarations.none
    override def codeOnly: Option[String] = Some(scalaType)

  /** A Definition given its meaning where it is written (`define`; where, `in`). */
  def onTheSpot[A: LeanType](spot: OnTheSpot): Definition[A] = new Definition[A](SymbolName(spot.name.value), "",
    Some(spot), WrittenAt.none)

  /** How a mention of the Definition reads, as a term of type `F`: its symbol; a define's call by name, noting the
    * define.
    */
  private def called[F](name: SymbolName, means: String, spot: Option[OnTheSpot], t: LeanType[?]): Final[F] =
    (spot, t.codeOnly) match
      case (None, Some(scala))                          => Symbols.codeOnly[F](name, means, scala)
      case (None, None)                                 => Symbols.term[F](name, means, ValueKind.Definition, t)
      case (Some(OnTheSpot(n, _, lambda, Spot.Define(b))), _) =>
        [T[_]] => (s: Sym[T]) => s.noted(Notes.of(Declarations.define(n, lambda)),
          s.define(b).asInstanceOf[T[F]]) // `b` was built at the curried type of the `define`'s own `F`
  /** The application, saying which Definition it applies and to what (`Called`). */
  private def called[R](d: Definition[?], args: List[Term[?]], t: Term[R]): Term[R] =
    Called(d.name, args, t.run)(using t.leanType)

  /** `d` applied to `args` as the function it is: what the extensions below make of a Definition whose type Scala
    * knows; of none, the Definition itself.
    */
  private[dsl] def applied[R: LeanType](d: Definition[?], args: List[Term[?]]): Term[R] =
    if args.isEmpty then d.asInstanceOf[Term[R]] // a word of no input is its own value
    else
      val f = d.curried[Any](using d.leanType.asInstanceOf[LeanType[Any]])
      called(d, args, Term[R]([T[_]] => (s: Sym[T]) => args.foldLeft(f.run(s))((g, a) =>
        s.app[Any, Any](g.asInstanceOf[T[Any => Any]], a.run(s).asInstanceOf[T[Any]])).asInstanceOf[T[R]]))

  extension [A, R](d: Definition[A => R])
    def apply(a: Term[A])(using LeanType[R]): Term[R] =
      called(d, List(a), Term.app(d.curried[A => R](using d.leanType), a))
  extension [A, B, R](d: Definition[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using LeanType[A], LeanType[B], LeanType[R]): Term[R] =
      called(d, List(a, b), Term.app(Term.app(d.curried[A => B => R], a), b))
  extension [A, B, C, R](d: Definition[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using LeanType[A], LeanType[B], LeanType[C], LeanType[R]): Term[R] =
      called(d, List(a, b, c), Term.app(Term.app(Term.app(d.curried[A => B => C => R], a), b), c))
  extension [A, B, C, D, R](d: Definition[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(
        using LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[R]): Term[R] =
      called(d, List(a, b, c, e),
        Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => R], a), b), c), e))
  extension [A, B, C, D, E, R](d: Definition[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E])(
        using LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[E], LeanType[R]): Term[R] =
      called(d, List(a, b, c, e, f),
        Term.app(Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => E => R], a), b), c), e), f))
  extension [A, B, C, D, E, G, R](d: Definition[(A, B, C, D, E, G) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[G])(
        using LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[E], LeanType[G], LeanType[R]): Term[R] =
      called(d, List(a, b, c, e, f, g), Term.app(Term.app(Term.app(Term.app(Term.app(Term.app(
        d.curried[A => B => C => D => E => G => R], a), b), c), e), f), g))
