package frflow.dsl.vocab

import frflow.core.term.language.Sym
import frflow.core.term.World
import frflow.dsl.build.Fault
import frflow.dsl.run.{RunNote, Worlds}
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.dsl.vocab.{Called, Stating}
import scala.annotation.unused


/** The combinators as programs write them on a pair, `(a, b).parTupled`; and, in a statement, a program's run from
  * the world the statement holds in (owner §41): `book(request).result`, what it returns, and `book(request).after`,
  * the world it leaves (`storedBookings.in(book(request).after)`). A run of a program that can fail, its Definition
  * `.failsWith[E]` (owner §46), is a `Run`: its `result` is the error (`Left`) or what it returns (`Right`), and
  * `after` the world either leaves. A run is of the statement's own variables (`Fault.RunInside` otherwise).
  */
object FlowSyntax:
  extension [A: LeanType, B: LeanType](p: (Flow[A], Flow[B]))
    def parTupled: Flow[(A, B)] = Flow.parTupled(p._1, p._2)

  extension [R](run: Term[Flow[R]])(using LeanType[R])
    /** What the run returns: a program that can fail is declared so (`.failsWith[E]`), and its run is a `Run`, whose
      * own `result` is an `Either[E, R]`.
      */
    def result: Term[R] = FlowSyntax.part[R](run, None, outcome = true)
  extension [R](run: Term[Flow[R]])
    /** The world the run leaves. */
    def after: Term[World] = FlowSyntax.part[World](run, None, outcome = false)

  extension [A](t: Term[A])
    /** What `t` reads of the world, read in `world` (`ofRoom(room).in(book(request).after)`). */
    def in(world: Term[World])(using st: Stating): Term[A] =
      if st.closing then Worlds.in(t, world) else Worlds.within(t, world)
    /** What `t` reads of the world, read in the world the statement holds in, named: before any run it reads. */
    def current: Term[A] = Worlds.within(t, Worlds.now)
    /** That no run of any program from the world the statement holds in changes `t`, whatever its outcome (owner
      * §44, §45 A): of a stretch of steps where a condition holds, `c implies t.isConstant`, `t` stays the same.
      * Proven of each program that changes what `t` reads; of a Declaration, assumed.
      */
    def isConstant(using @unused st: Stating): Term[Boolean] = Worlds.constant(t)

  /** The run's outcome or world after, a variable its note names until the statement is closed; of a program
    * applied to a variable bound inside the statement, a fault.
    */
  private[vocab] def part[A: LeanType](run: Term[?], error: Option[LeanType[?]], outcome: Boolean): Term[A] =
    Term.exprOf(run).fold {
      val fault = Fault.RunInside(Called.of(run).fold("a program")(_._1.value))
      Term.noted(Notes.fault(fault))([T[_]] => (s: Sym[T]) => s.free[A](Worlds.binder))
    } { key =>
      val note = RunNote(key, error.map(_.ty), run)
      val x = if outcome then note.outcome else note.after
      Term.noted(Notes.of(LeanType[A].declares))([T[_]] => (s: Sym[T]) => s.noted(note, s.free[A](x)))
    }
