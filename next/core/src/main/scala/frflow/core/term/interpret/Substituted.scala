package frflow.core.term.interpret

import frflow.core.expr.Binder
import frflow.core.term.{Ext, Sym}

/** Each free variable `env` names as the value it gives, every other operation as `base` has it: a term written over
  * free variables (a statement's leading variables opened, its current world, its runs' outcomes) closed by the
  * binders that give them (owner §41, `dsl.node.Closing`). A variable is named by its whole binder, so two runs'
  * outcomes, told apart by their binders' names, are never one.
  */
final class Substituted[T[_]](protected val base: Sym[T], env: Map[Binder, T[Any]]) extends Forward[T, T]:
  protected def fwd[A](t: T[A]): T[A] = t
  protected def bwd[A](u: T[A]): T[A] = u
  /** The value `env` gives the variable, of the variable's own type: each is bound at its binder's type. */
  override def free[A](x: Binder): T[A] = env.get(x).fold(base.free(x))(_.asInstanceOf[T[A]])
  override def extension[E[_[_]]](key: Ext[E]): Option[E[T]] = base.extension(key)
