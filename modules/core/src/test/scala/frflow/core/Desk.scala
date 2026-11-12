package frflow.core

import frflow.core.code.Code
import frflow.core.expr.Binder
import frflow.core.name.{DefName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}

/** A booking desk: a Definition `book` of a booking, its proven code a define that grants every one, and a claim
  * that it does. A valid theory.
  */
object Desk:
  val book: SymbolName = SymbolName("book")
  val bookTy: Ty = Ty.FnOf(List(Booking.ty), Ty.Bool)

  private val b = Binder(VarId.level(0), "b", Booking.ty)
  private val granted: Final[Boolean] = [T[_]] => (s: Sym[T]) => s.bool(true)

  val code: Define = Define(DefName("bookIfFree"), Written.lambda(List(b), granted, SourceText("bookIfFree")),
    DefineForm.Function)

  /** Every booking is granted. */
  val bookRuns: spec.Node = Nodes.claim("bookRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.call(l.sym[Booking => Boolean]("book", bookTy), x))))

  val kb: Kb = Kb.of(bookRuns)
    .declaring(_.copy(types = List(Booking.data), defines = List(code)))
    .naming(Nodes.definition("book", bookTy))
    .coding(book -> Code.Proven(DefName("bookIfFree")))
