package frflow.dsl.run

import frflow.core.expr.{Binder, Expr}
import frflow.core.name.VarId
import frflow.core.term.Annotation
import frflow.core.ty.Ty
import frflow.dsl.term.Term

/** A run of a program from the world a statement holds in, as a statement reads it (`book(request).after`): the
  * program applied (`key` its IR, over the statement's leading variables), and the error it may fail with, which its
  * Definition declares (`failsWith`, owner §46: the run is then read with both outcomes). Its outcome and the world
  * after are variables named by the run itself (`VarId.ran`, the run's IR and reading in the binder's name, so two
  * runs' variables are two) until the statement is closed (`node.Closing` binds them by a run from the current world).
  */
final case class RunNote(key: Expr, error: Option[Ty], program: Term[?]) extends Annotation:
  /** What the run gives: the program's result, or, read as failing, its error or its result. */
  def outcomeType: Ty =
    val result = program.leanType.ty match
      case Ty.FlowOf(r, _) => r
      case other           => other
    error.fold(result)(Ty.EitherOf(_, result))
  def outcome: Binder = Binder(VarId.ran(0), s"result of $name", outcomeType)
  def after: Binder = Binder(VarId.ran(1), s"after $name", Ty.World)
  /** The run, structurally: its program's IR and how the statement reads it. */
  private def name: String = error.fold(key.toString)(e => s"$key failing with $e")
