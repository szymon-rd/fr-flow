package frflow.dsl.build

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.ty.Ty

/** The supply of fresh variables for one scope: an elaboration, or the building of an implementation's flow while it
  * runs (`eval.run.FlowRun`). Ambient, since the developer's lambdas are plain functions and cannot be passed it.
  */
object Fresh:
  private val next: ThreadLocal[Option[VarId]] = ThreadLocal.withInitial(() => None)

  def active: Boolean = next.get.isDefined

  /** A variable no other of this scope has; outside a scope, a FrFlow bug. */
  def binder(hint: String, ty: Ty): Binder = next.get match
    case Some(id) =>
      next.set(Some(id.next))
      Binder(id, hint, ty)
    case None => throw IllegalStateException("FrFlow bug: a term built outside elaboration and outside a run")

  def within[A](body: => A): A =
    val outer = next.get
    next.set(Some(VarId(0)))
    try body
    finally next.set(outer)
