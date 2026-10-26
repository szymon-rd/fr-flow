package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.term.{Final, Sym}
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Declarations, Fault, Source}
import frflow.dsl.term.{LeanType, Notes, Term}
import scala.annotation.publicInBinary

/** A value code and programs use (owner §15), of any type: a function (`val granted =
  * Definition[(RoomBookings, Booking) => Boolean]("whether …")`), a program (`Booking => Program[Boolean]`), a plain
  * value. Named as its val. It gets its meaning once: from the knowledge base (`implementProven`, `implementTested`,
  * `implementValue`, `implementProvided`), or where it is written: `define { … }` and `program { … }` are
  * Definitions carrying their proven code (`onTheSpot`). Every claim mentioning it constrains it, and its code is
  * checked against them.
  */
final class Definition[A] @publicInBinary private[dsl] (val name: SymbolName, val means: String,
    val onTheSpot: Option[OnTheSpot])(using t: LeanType[A])
    extends Term[A](Definition.called[A](name, means, onTheSpot, t)):
  /** The term as a curried function (`F` the curried type of `A`): what `Functions.app` applies. */
  def curried[F: LeanType]: Term[F] = Term(Definition.called[F](name, means, onTheSpot, t))

object Definition:
  inline def apply[A: LeanType](means: String): Definition[A] =
    new Definition[A](SymbolName(Source.valName), means, None)

  /** A Definition given its meaning where it is written (`define`, `program`). */
  def onTheSpot[A: LeanType](spot: OnTheSpot): Definition[A] = new Definition[A](SymbolName(spot.name.value), "",
    Some(spot))

  /** How a mention of the Definition reads, as a term of type `F`: its symbol; a define's call by name, noting the
    * define; a program, a fault (claims speak of the Definition the program is the meaning of).
    */
  private def called[F](name: SymbolName, means: String, spot: Option[OnTheSpot], t: LeanType[?]): Final[F] =
    spot match
      case None                               => Symbols.term[F](name, means, ValueKind.Definition, t)
      case Some(OnTheSpot(n, _, lambda, Some(b))) =>
        [T[_]] => (s: Sym[T]) => s.noted(Notes.of(Declarations.define(n, lambda)),
          s.define(b).asInstanceOf[T[F]]) // `b` was built at the curried type of the `define`'s own `F`
      case Some(OnTheSpot(n, _, _, None))     =>
        [T[_]] => (s: Sym[T]) => s.noted(Notes.fault(Fault.ProgramMentioned(n.value)), s.param[F](name, t.ty))

  extension [A, R](d: Definition[A => R])
    def apply(a: Term[A])(using LeanType[R]): Term[R] = Term.app(d.curried[A => R](using d.leanType), a)
  extension [A, B, R](d: Definition[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using LeanType[A], LeanType[B], LeanType[R]): Term[R] =
      Term.app(Term.app(d.curried[A => B => R], a), b)
  extension [A, B, C, R](d: Definition[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using LeanType[A], LeanType[B], LeanType[C], LeanType[R]): Term[R] =
      Term.app(Term.app(Term.app(d.curried[A => B => C => R], a), b), c)
  extension [A, B, C, D, R](d: Definition[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(
        using LeanType[A], LeanType[B], LeanType[C], LeanType[D], LeanType[R]): Term[R] =
      Term.app(Term.app(Term.app(Term.app(d.curried[A => B => C => D => R], a), b), c), e)
  // … to six inputs.
