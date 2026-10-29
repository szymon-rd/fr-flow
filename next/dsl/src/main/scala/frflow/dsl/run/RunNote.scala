package frflow.dsl.run

import frflow.core.expr.{Binder, Expr}
import frflow.core.name.VarId
import frflow.core.term.Annotation
import frflow.core.ty.Ty
import frflow.dsl.term.Term

/** A run of a program from the world a statement holds in, as a statement reads it (`book(request).after`): the
  * program applied (`key` its IR, over the statement's leading variables), and the error it may fail with when the
  * statement reads it as failing (`.failing[E]`). Its outcome and the world after are variables named by the run
  * until the statement is closed (`node.Closing` binds them by a run from the current world).
  */
final case class RunNote(key: Expr, error: Option[Ty], program: Term[?]) extends Annotation:
  /** What the run gives: the program's result, or, read as failing, its error or its result. */
  def outcomeType: Ty =
    val result = program.leanType.ty match
      case Ty.FlowOf(r, _) => r
      case other           => other
    error.fold(result)(Ty.EitherOf(_, result))
  def outcome: Binder = Binder(VarId.ran(id, 0), "result", outcomeType)
  def after: Binder = Binder(VarId.ran(id, 1), "after", Ty.World)
  private def id: Int = (key, error).hashCode
