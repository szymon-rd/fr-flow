package frflow.dsl.vocab

import frflow.core.term.language.Sym
import frflow.core.term.World
import frflow.dsl.run.Worlds
import frflow.dsl.term.{LeanType, Term}

/** A program that can fail with an `E` applied, in a statement (owner §46: its Definition `.failsWith[E]`): its run
  * from the world the statement holds in is read with both outcomes. `result` is the error (`Left`) or what it gives
  * (`Right`), and `after` the world either leaves (`node.Closing`: `runs ∧ fails`), so a statement about it says what
  * a failing run does too.
  */
final class Run[E, R](program: Term[Flow[R]])(using val error: LeanType[E], r: LeanType[R])
    extends Term[Flow[R]](program.run)(using program.leanType):
  def result: Term[Either[E, R]] = FlowSyntax.part[Either[E, R]](program, Some(error), outcome = true)
  def after: Term[World] = FlowSyntax.part[World](program, Some(error), outcome = false)
  /** Every model's state after the run is its state before (the faults its failing calls take are no model's). */
  def changesNothing: Term[Boolean] = Term.both(after, Worlds.now)([T[_]] => (s: Sym[T]) => s.unchanged)
