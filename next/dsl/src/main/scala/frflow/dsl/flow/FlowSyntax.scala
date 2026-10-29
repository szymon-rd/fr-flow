package frflow.dsl.flow

import frflow.core.term.{Sym, World}
import frflow.core.term.interpret.ToExpr
import frflow.dsl.build.Fault
import frflow.dsl.run.{RunNote, Worlds}
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.dsl.vocab.Called
import scala.util.control.NonFatal

/** The combinators as programs write them on a pair, `(a, b).parTupled`; and, in a statement, a program's run from
  * the world the statement holds in (owner §41): `book(request).result`, what it returns, and `book(request).after`,
  * the world it leaves (`storedBookings.in(book(request).after)`). A run of a program that can fail is read as
  * failing, `p.failing[E]`: its `result` is then the error (`Left`) or what it returns (`Right`), and `after` the
  * world either leaves. A run is of the statement's own variables (`Fault.RunInside` otherwise).
  */
object FlowSyntax:
  extension [A: LeanType, B: LeanType](p: (Flow[A], Flow[B]))
    def parTupled: Flow[(A, B)] = Flow.parTupled(p._1, p._2)

  extension [R](run: Term[Flow[R]])(using LeanType[R])
    /** What the run returns; of a program that can fail, of the runs that succeed. */
    def result: Term[R] = FlowSyntax.part[R](run, None, outcome = true)
    def failing[E: LeanType]: Failing[R, E] = Failing(run)
  extension [R](run: Term[Flow[R]])
    /** The world the run leaves; of a program that can fail, of the runs that succeed. */
    def after: Term[World] = FlowSyntax.part[World](run, None, outcome = false)

  /** A run read as failing with an `E`: both its outcomes. */
  final class Failing[R: LeanType, E: LeanType](run: Term[Flow[R]]):
    def result: Term[Either[E, R]] = FlowSyntax.part[Either[E, R]](run, Some(LeanType[E]), outcome = true)
    def after: Term[World] = FlowSyntax.part[World](run, Some(LeanType[E]), outcome = false)
    /** Every model's state after the run is its state before (the faults its failing calls take are no model's). */
    def changesNothing: Term[Boolean] = Term.both(after, Worlds.current)([T[_]] => (s: Sym[T]) => s.unchanged)

  /** The run's outcome or world after, a variable its note names until the statement is closed; of a program
    * applied to a variable bound inside the statement, a fault.
    */
  private def part[A: LeanType](run: Term[?], error: Option[LeanType[?]], outcome: Boolean): Term[A] =
    try
      val note = RunNote(ToExpr.of(run.run), error.map(_.ty), run)
      val x = if outcome then note.outcome else note.after
      Term.noted(Notes.of(LeanType[A].declares))([T[_]] => (s: Sym[T]) => s.noted(note, s.free[A](x)))
    catch case NonFatal(_) =>
      val fault = Fault.RunInside(Called.of(run).fold("a program")(_._1.value))
      Term.noted(Notes.fault(fault))([T[_]] => (s: Sym[T]) => s.free[A](Worlds.binder))
